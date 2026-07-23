# -*- coding: utf-8 -*-
#
# Gramps - a GTK+/GNOME based genealogy program
#
# Copyright (C) 2010-2012  Gary Burton
#                          GraphvizSvgParser is based on the Gramps XML import
#                          DotSvgGenerator is based on the relationship graph
#                          report.
#                          Mouse panning is derived from the pedigree view
# Copyright (C) 2012       Mathieu MD
# Copyright (C) 2015-      Serge Noiraud
# Copyright (C) 2016-      Ivan Komaritsyn
#
# Modified in 2026 for the Graph View Profiles project.
# Project website: https://myown-project.dk/
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
#

# $Id$

#-------------------------------------------------------------------------
#
# Python modules
#
#-------------------------------------------------------------------------
import os
import json
import logging
import tempfile
from functools import wraps
from re import MULTILINE, findall
from xml.parsers.expat import ParserCreate
import string
from subprocess import Popen, PIPE
from io import StringIO
from threading import Thread
from math import sqrt, pow
from html import escape
from datetime import datetime
from collections import abc, deque
import gi
from gi.repository import Gtk, Gdk, GdkPixbuf, GLib, Pango

#-------------------------------------------------------------------------
#
# Gramps Modules
#
#-------------------------------------------------------------------------
from gramps.gen import datehandler
from gramps.gen.config import config
from gramps.gen.constfunc import win
from gramps.gen.db import DbTxn
from gramps.gen.display.name import displayer
from gramps.gen.display.place import displayer as place_displayer
from gramps.gen.errors import WindowActiveError
from gramps.gen.lib import (Person, Family, ChildRef, Name, Surname,
                            ChildRefType, Event, EventRef, EventType, EventRoleType)
from gramps.gen.utils.alive import probably_alive
from gramps.gen.utils.callback import Callback
from gramps.gen.utils.db import (get_birth_or_fallback, get_death_or_fallback,
                                 find_children, find_parents, preset_name,
                                 find_witnessed_people)
from gramps.gen.utils.file import search_for, media_path_full, find_file
from gramps.gen.utils.libformatting import FormattingHelper
from gramps.gen.utils.thumbnails import get_thumbnail_path

from gramps.gui.dialog import (OptionDialog, ErrorDialog, QuestionDialog2,
                               WarningDialog)
from gramps.gui.display import display_url
from gramps.gui.editors import EditPerson, EditFamily, EditTagList, EditEventRef
from gramps.gui.utils import (color_graph_box, color_graph_family,
                              rgb_to_hex, hex_to_rgb_float,
                              process_pending_events)
from gramps.gui.views.navigationview import NavigationView
from gramps.gui.views.bookmarks import PersonBookmarks
from gramps.gui.views.tags import OrganizeTagsDialog
from gramps.gui.widgets import progressdialog as progressdlg
from gramps.gui.widgets.menuitem import add_menuitem
from gramps.gen.utils.symbols import Symbols

from gramps.gui.pluginmanager import GuiPluginManager
from gramps.gen.plug import CATEGORY_QR_PERSON, CATEGORY_QR_FAMILY
from gramps.gui.plug.quick import run_report

from gramps.gen.filters import GenericFilterFactory, rules

from gramps.gen.const import GRAMPS_LOCALE as glocale
try:
    _trans = glocale.get_addon_translator(__file__)
except ValueError:
    _trans = glocale.translation
_ = _trans.gettext

if win():
    DETACHED_PROCESS = 8

for goo_ver in ('3.0', '2.0'):
    try:
        gi.require_version('GooCanvas', goo_ver)
        from gi.repository import GooCanvas
        _GOO = True
        break
    except (ImportError, ValueError):
        _GOO = False

if os.sys.platform == "win32":
    _DOT_FOUND = search_for("dot.exe")
else:
    _DOT_FOUND = search_for("dot")

SPLINE = {0: 'false', 1: 'true', 2: 'ortho'}

FAMILY_TAG = "ProfileTag"

WIKI_PAGE = 'https://gramps-project.org/wiki/index.php?title=Graph_View'


def batch_profile_graph_refresh(redraw_after=True):
    """
    Suppress intermediate GraphWidget.populate() calls during profile work.

    Nested profile functions share the same counter. Only the outermost
    successful Standard/View load performs one final graph rebuild.
    Temporary close-time restoration uses redraw_after=False.
    """
    def decorator(func):
        @wraps(func)
        def wrapped(self, *args, **kwargs):
            outermost = (
                getattr(self, '_profile_graph_refresh_depth', 0) == 0)
            self._profile_graph_refresh_depth = (
                getattr(self, '_profile_graph_refresh_depth', 0) + 1)
            succeeded = False

            try:
                result = func(self, *args, **kwargs)
                succeeded = bool(result)
                return result
            finally:
                self._profile_graph_refresh_depth = max(
                    getattr(self, '_profile_graph_refresh_depth', 1) - 1, 0)

                if (outermost and redraw_after and succeeded and
                        self.graph_widget is not None):
                    try:
                        active_handle = self.get_active()
                    except Exception:
                        active_handle = ''

                    if active_handle:
                        self.graph_widget.populate(active_handle)

        return wrapped
    return decorator


# gtk version
gtk_version = float("%s.%s" % (Gtk.MAJOR_VERSION, Gtk.MINOR_VERSION))

#-------------------------------------------------------------------------
#
# GraphView modules
#
#-------------------------------------------------------------------------
import sys
sys.path.append(os.path.abspath(os.path.dirname(__file__)))
from search_widget import SearchWidget, Popover, ListBoxRow, get_person_tooltip
from avatars import Avatars


#-------------------------------------------------------------------------
#
# GraphView
#
#-------------------------------------------------------------------------
class GraphView(NavigationView):
    """
    View for pedigree tree.
    Displays the ancestors and descendants of a selected individual.
    """
    # default settings in the config file
    CONFIGSETTINGS = (
        ('interface.graphview-show-images', True),
        ('interface.graphview-show-id', True),
        ('interface.graphview-show-avatars', True),
        ('interface.graphview-avatars-style', 1),
        ('interface.graphview-avatars-male', ''),       # custom avatar
        ('interface.graphview-avatars-female', ''),     # custom avatar
        ('interface.graphview-avatars-unknown', ''),    # custom avatar
        ('interface.graphview-avatars-other', ''),      # custom avatar
        ('interface.graphview-show-full-dates', False),
        ('interface.graphview-show-places', False),
        ('interface.graphview-place-format', 0),
        ('interface.graphview-show-lines', 1),
        ('interface.graphview-show-tags', False),
        ('interface.graphview-filter-family-tag', False),
        ('interface.graphview-highlight-home-person', True),
        ('interface.graphview-home-path-color', '#000000'),
        ('interface.graphview-descendant-generations', 10),
        ('interface.graphview-ancestor-generations', 3),
        ('interface.graphview-people-limit', 1000),
        ('interface.graphview-show-animation', True),
        ('interface.graphview-animation-speed', 3),
        ('interface.graphview-animation-count', 4),
        ('interface.graphview-search-all-db', True),
        ('interface.graphview-search-show-images', True),
        ('interface.graphview-search-marked-first', True),
        ('interface.graphview-ranksep', 5),
        ('interface.graphview-nodesep', 2),
        ('interface.graphview-person-theme', 0),
        ('interface.graphview-scale', 1),
        ('interface.graphview-person-border-size', 1),
        ('interface.graphview-active-person-border-size', 3),
        ('interface.graphview-font', ['', 14]),
        ('interface.graphview-direction', 0),
        ('interface.graphview-show-all-connected', False))

    def __init__(self, pdata, dbstate, uistate, nav_group=0):
        NavigationView.__init__(self, _('Graph View'), pdata, dbstate, uistate,
                                PersonBookmarks, nav_group)

        self.show_images = self._config.get('interface.graphview-show-images')
        self.show_ID = self._config.get('interface.graphview-show-id')
        self.show_full_dates = self._config.get(
            'interface.graphview-show-full-dates')
        self.show_places = self._config.get('interface.graphview-show-places')
        self.show_tag_color = self._config.get('interface.graphview-show-tags')
        self.highlight_home_person = self._config.get(
            'interface.graphview-highlight-home-person')
        self.home_path_color = self._config.get(
            'interface.graphview-home-path-color')
        self.descendant_generations = self._config.get(
            'interface.graphview-descendant-generations')
        self.ancestor_generations = self._config.get(
            'interface.graphview-ancestor-generations')
        self.people_limit = self._config.get(
            'interface.graphview-people-limit')

        self.dbstate = dbstate
        self.uistate = uistate
        self.graph_widget = None

        # Startup profile handling is checked once per
        # database/opened family tree.
        self.standard_profile_auto_checked = False
        self.standard_profile_auto_scheduled = False
        self.standard_profile_prompted = False
        # A valid startup profile may create the first graph
        # directly, so build_tree must not immediately redraw it.
        self.startup_profile_created_initial_graph = False

        # View profile load-only group choices include
        # Time direction, Limit number, Theme, Path color, Font, Active
        # person border size, Person border size, Line types, Generations,
        # Spacings and Zoom & chart position.
        # Remember the currently loaded/saved View profile.
        # This makes it possible to save small later changes back to the
        # same file without choosing a filename again.
        self.current_view_profile_filename = ''
        self.current_view_profile_name = ''
        self.current_view_profile_status_label = None
        self.standard_profile_status_label = None
        self.standard_profile_load_button = None
        # A saved Standard file is not shown as active content
        # until it has been saved or loaded in the current book session.
        self.standard_profile_controls_active = False
        self.profile_feature_enable_checkbox = None
        self.profile_temporary_checkbox = None
        self.temporary_profile_restore_snapshot_created = False
        self.temporary_profile_restore_profile_loaded = False
        # Remember the temp snapshot for the currently
        # opened book and whether the user wants it restored on close.
        # The filename is stored because db context may already be changing
        # when Gramps starts closing/switching books.
        self.temporary_profile_restore_snapshot_filename = ''
        self.temporary_profile_restore_enabled_for_open_book = False
        self.temporary_profile_restore_restored = False
        # Snapshot write failures must never block profile
        # loading. Keep the last write error for one useful warning and allow
        # temporary use to be forced off for the current open book even if the
        # startup JSON itself cannot be rewritten.
        self.temporary_profile_restore_snapshot_last_error = ''
        self.temporary_profile_restore_forced_off_for_open_book = False
        self.profile_function_controls = []
        self.updating_profile_startup_controls = False
        self.profile_startup_none_radio = None
        self.profile_startup_standard_radio = None
        self.profile_startup_view_radio = None
        self.current_view_profile_save_button = None
        self.current_view_profile_delete_button = None
        self.standard_profile_delete_button = None
        # Keep a reference to the open Configure/Layout
        # spinner for Limit number displayed. Profile loads update the
        # config value immediately, but the already-open spinner needs a
        # small manual sync so the visible number changes without closing
        # and reopening Configure.
        self.people_limit_config_spinner = None
        self.profiles_page_has_unsaved_changes = False
        self.profiles_config_window = None
        self.profiles_config_delete_handler_id = None
        self.profiles_config_response_handler_id = None
        self.profiles_config_close_button_ids = set()
        # The direct Close-button guard detects the
        # user's attempt to close and opens the unsaved warning.
        # request_profiles_configure_close() has a different job: after
        # "Close anyway", it closes Configure through its normal GTK response
        # path, so the warning and Configure disappear in the same action.
        self.profiles_config_force_close_once = False
        # No View profile loaded means a clean View
        # column. The user selects what a new View profile should contain.
        self.view_profile_save_choices = self.get_empty_view_profile_save_choices()
        self.profile_view_checkbox_info = []
        self.updating_view_profile_controls = False
        self.profile_standard_checkbox_info = []
        self.updating_standard_profile_controls = False

        # Profile loading may change many shared config values.
        # GraphWidget.populate() is suppressed until the whole load is ready.
        self._profile_graph_refresh_depth = 0

        self.dbstate.connect('database-changed', self.change_db)

        # dict {handle, tooltip_str} of tooltips in markup format
        self.tags_tooltips = {}

        # for disable animation options in config dialog
        self.ani_widgets = []
        # for disable custom avatar options in config dialog
        self.avatar_widgets = []
        # Show avatars depends on Show images only inside
        # Standard/View profile choices. The original Layout and Themes
        # controls must keep their normal GraphView behaviour.
        self.profile_standard_show_images_checkbox = None
        self.profile_standard_show_avatars_checkbox = None
        self.profile_view_show_images_checkbox = None
        self.profile_view_show_avatars_checkbox = None
        # Limit number displayed is always stored in profile
        # JSON. The profile checkbox is available only for values above 0.
        self.profile_standard_people_limit_checkbox = None
        self.profile_view_people_limit_checkbox = None
        # Keep references to the ordinary Layout and Themes
        # widgets while Configure is open. Profile loads already update the
        # shared config values; these references let the visible controls
        # follow immediately without closing and reopening Configure.
        self.open_graphview_configdialog = None
        self.open_config_widgets = {}
        self.home_path_color_config_label = None

        self.additional_uis.append(self.additional_ui)
        self.define_print_actions()
        self.uistate.connect('font-changed', self.font_changed)

    def set_profile_config_values_all_connected_last(
            self, allowed_config_keys, values):
        """
        Apply one profile config batch with All connected as the final value.

        Graph rebuilds are suppressed by batch_profile_graph_refresh while
        this helper is used from Standard/View load or temporary restoration.
        """
        all_connected_key = 'interface.graphview-show-all-connected'

        for config_key in allowed_config_keys:
            if config_key == all_connected_key:
                continue
            if config_key in values:
                self._config.set(config_key, values[config_key])

        if (all_connected_key in allowed_config_keys and
                all_connected_key in values):
            self._config.set(
                all_connected_key, values[all_connected_key])

    def on_delete(self):
        """
        Method called on shutdown.
        See PageView class (../gramps/gui/views/pageview.py).
        """
        # If profiles are used temporarily, restore the
        # book-opening GraphView settings before Gramps writes shared config.
        self.restore_temporary_profile_settings_on_close()
        super().on_delete()
        # stop search to allow close app properly
        self.graph_widget.search_widget.stop_search()

    def font_changed(self):
        self.graph_widget.font_changed(self.get_active())
        #self.goto_handle(None)

    def define_print_actions(self):
        """
        Associate the print button to the PrintView action.
        """
        self._add_action('PrintView', self.printview, "<PRIMARY><SHIFT>P")
        self._add_action('PRIMARY-J', self.jump, '<PRIMARY>J')

    def _connect_db_signals(self):
        """
        Set up callbacks for changes to person and family nodes.
        """
        self.callman.add_db_signal('person-update', self.goto_handle)
        self.callman.add_db_signal('family-update', self.goto_handle)
        self.callman.add_db_signal('event-update', self.goto_handle)

    def change_db(self, _db):
        """
        Set up callback for changes to the database.
        """
        # Restore only when this GraphView instance already has
        # a snapshot for a genuinely open previous book. On the first
        # database-changed signal after starting Gramps there is no previous
        # in-memory book snapshot. Reading an old temp file at that point
        # would replace the current shared Gramps config before the new
        # book-opening snapshot is written, effectively recycling yesterday's
        # temp values. A real book switch has both markers set and still
        # restores the book being left before changing database context.
        if (self.temporary_profile_restore_snapshot_created and
                self.temporary_profile_restore_snapshot_filename):
            self.restore_temporary_profile_settings_on_close()
        self._change_db(_db)

        # ProfileTag is a current-book choice unless a profile
        # explicitly loads it. GraphView config is shared between family
        # trees, so clear a value left by the previous book before creating
        # the new book's temporary snapshot or loading its startup profile.
        self.reset_family_tag_filter_at_book_open()

        self.standard_profile_auto_checked = False
        self.standard_profile_auto_scheduled = False
        self.standard_profile_prompted = False
        self.startup_profile_created_initial_graph = False
        self.standard_profile_controls_active = False
        self.set_current_view_profile('', '')
        self.reset_view_profile_save_choices()
        # Each opened family tree must get a fresh
        # temporary restore snapshot as early as possible. GraphView
        # settings are shared between books, and a startup profile can
        # change them before the user opens Configure.
        self.temporary_profile_restore_snapshot_created = False
        self.temporary_profile_restore_profile_loaded = False
        self.temporary_profile_restore_snapshot_filename = ''
        self.temporary_profile_restore_enabled_for_open_book = False
        self.temporary_profile_restore_restored = False
        self.temporary_profile_restore_snapshot_last_error = ''
        self.temporary_profile_restore_forced_off_for_open_book = False
        self.graph_widget.scale = self._config.get(
            'interface.graphview-scale')
        self.create_temporary_profile_restore_snapshot_at_book_open(
            force=True)

        if self.active:
            if self.get_active() != "":
                self.graph_widget.set_available(True)

                # Load a valid startup profile before GraphView
                # creates its ordinary first graph. The profile loader already
                # performs the one final populate(). If no usable startup
                # profile exists, fall back to normal GraphView startup.
                if not self.auto_load_or_offer_standard_profile():
                    self.graph_widget.populate(self.get_active())
                    self.schedule_auto_load_standard_profile()
            else:
                self.graph_widget.set_available(False)
        else:
            self.dirty = True
            self.graph_widget.set_available(False)

    def get_stock(self):
        """
        The category stock icon.
        """
        return 'gramps-pedigree'

    def get_viewtype_stock(self):
        """
        Type of view in category.
        """
        return 'gramps-pedigree'

    def build_widget(self):
        """
        Builds the widget with canvas and controls.
        """
        self.graph_widget = GraphWidget(self, self.dbstate, self.uistate)
        return self.graph_widget.get_widget()

    def build_tree(self):
        """
        There is no separate step to fill the widget with data.
        The data is populated as part of canvas widget construction.
        It can be called to rebuild tree.
        """
        if self.active:
            if self.get_active() != "":
                # Retry the book-open snapshot here if
                # change_db ran before the database context was ready.
                self.create_temporary_profile_restore_snapshot_at_book_open()

                # Change_db may already have loaded the selected
                # startup profile and created the first graph.
                if self.startup_profile_created_initial_graph:
                    return

                if not self.auto_load_or_offer_standard_profile():
                    self.graph_widget.populate(self.get_active())
                    self.schedule_auto_load_standard_profile()

    additional_ui = [  # Defines the UI string for UIManager
        '''
      <placeholder id="CommonGo">
      <section>
        <item>
          <attribute name="action">win.Back</attribute>
          <attribute name="label" translatable="yes">_Back</attribute>
        </item>
        <item>
          <attribute name="action">win.Forward</attribute>
          <attribute name="label" translatable="yes">_Forward</attribute>
        </item>
      </section>
      <section>
        <item>
          <attribute name="action">win.HomePerson</attribute>
          <attribute name="label" translatable="yes">_Home</attribute>
        </item>
      </section>
      </placeholder>
''',
        '''
      <section id='CommonEdit' groups='RW'>
        <item>
          <attribute name="action">win.PrintView</attribute>
          <attribute name="label" translatable="yes">_Print...</attribute>
        </item>
      </section>
''',  # Following are the Toolbar items
        '''
    <placeholder id='CommonNavigation'>
    <child groups='RO'>
      <object class="GtkToolButton">
        <property name="icon-name">go-previous</property>
        <property name="action-name">win.Back</property>
        <property name="tooltip_text" translatable="yes">'''
        '''Go to the previous object in the history</property>
        <property name="label" translatable="yes">_Back</property>
        <property name="use-underline">True</property>
      </object>
      <packing>
        <property name="homogeneous">False</property>
      </packing>
    </child>
    <child groups='RO'>
      <object class="GtkToolButton">
        <property name="icon-name">go-next</property>
        <property name="action-name">win.Forward</property>
        <property name="tooltip_text" translatable="yes">'''
        '''Go to the next object in the history</property>
        <property name="label" translatable="yes">_Forward</property>
        <property name="use-underline">True</property>
      </object>
      <packing>
        <property name="homogeneous">False</property>
      </packing>
    </child>
    <child groups='RO'>
      <object class="GtkToolButton">
        <property name="icon-name">go-home</property>
        <property name="action-name">win.HomePerson</property>
        <property name="tooltip_text" translatable="yes">'''
        '''Go to the default person</property>
        <property name="label" translatable="yes">_Home</property>
        <property name="use-underline">True</property>
      </object>
      <packing>
        <property name="homogeneous">False</property>
      </packing>
    </child>
    </placeholder>
''',
        '''
    <placeholder id='BarCommonEdit'>
    <child groups='RO'>
      <object class="GtkToolButton">
        <property name="icon-name">document-print</property>
        <property name="action-name">win.PrintView</property>
        <property name="tooltip_text" translatable="yes">"Save the dot file '''
        '''for a later print.\nThis will save a .gv file and a svg file.\n'''
        '''You must select a .gv file"</property>
        <property name="label" translatable="yes">_Print...</property>
        <property name="use-underline">True</property>
      </object>
      <packing>
        <property name="homogeneous">False</property>
      </packing>
    </child>
    </placeholder>
''']

    def navigation_type(self):
        """
        The type of forward and backward navigation to perform.
        """
        return 'Person'

    def goto_handle(self, handle):
        """
        Go to a named handle.
        """
        if self.active:
            if self.get_active() != "":
                self.graph_widget.populate(self.get_active())
                self.graph_widget.set_available(True)
        else:
            self.dirty = True
            self.graph_widget.set_available(False)

    def change_active_person(self, _menuitem=None, person_handle=''):
        """
        Change active person.
        """
        if person_handle:
            self.change_active(person_handle)

    def can_configure(self):
        """
        See :class:`~gui.views.pageview.PageView
        :return: bool
        """
        return True

    def cb_update_show_images(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the images setting.
        """
        self.show_images = entry == 'True'
        self.graph_widget.populate(self.get_active())

    def cb_update_show_ID(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the ID setting.
        """
        self.show_ID = entry == 'True'
        self.graph_widget.populate(self.get_active())

    def cb_update_show_avatars(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the avatars setting.
        """
        self.show_avatars = entry == 'True'
        self.graph_widget.populate(self.get_active())

    def apply_avatar_profile_save_rules(self, profile):
        """
        Normalize avatar values before a Standard/View profile is saved.

        Show avatars is always false when Show images is false. The five
        avatar style/custom-avatar keys are saved only when both options are
        true; otherwise the profile contains only the false avatar value.
        """
        if not isinstance(profile, dict):
            return profile

        display = profile.get('display')
        if not isinstance(display, dict):
            return profile

        images_enabled = bool(display.get(
            'interface.graphview-show-images', False))
        avatars_enabled = bool(
            images_enabled and display.get(
                'interface.graphview-show-avatars', False))
        display['interface.graphview-show-avatars'] = avatars_enabled

        if not avatars_enabled:
            style = profile.get('style')
            if isinstance(style, dict):
                for config_key in (
                        'interface.graphview-avatars-style',
                        'interface.graphview-avatars-male',
                        'interface.graphview-avatars-female',
                        'interface.graphview-avatars-unknown',
                        'interface.graphview-avatars-other'):
                    style.pop(config_key, None)

        return profile

    def apply_avatar_profile_load_rules(self, loaded_values):
        """
        Filter avatar values collected from a profile before loading them.

        Avatar style/custom values are accepted only when the profile itself
        explicitly contains Show images=true and Show avatars=true.
        """
        if not isinstance(loaded_values, dict):
            return loaded_values

        images_key = 'interface.graphview-show-images'
        avatars_key = 'interface.graphview-show-avatars'
        images_explicitly_true = (
            images_key in loaded_values and bool(loaded_values[images_key]))
        avatars_explicitly_true = (
            avatars_key in loaded_values and bool(loaded_values[avatars_key]))

        if images_key in loaded_values and not bool(loaded_values[images_key]):
            loaded_values[avatars_key] = False
            avatars_explicitly_true = False

        if not (images_explicitly_true and avatars_explicitly_true):
            for config_key in (
                    'interface.graphview-avatars-style',
                    'interface.graphview-avatars-male',
                    'interface.graphview-avatars-female',
                    'interface.graphview-avatars-unknown',
                    'interface.graphview-avatars-other'):
                loaded_values.pop(config_key, None)

        return loaded_values

    def update_profile_avatar_controls_sensitivity(self):
        """Keep avatar choices dependent on images in both columns."""
        column_info = (
            ('standard',
             getattr(self, 'profile_standard_show_images_checkbox', None),
             getattr(self, 'profile_standard_show_avatars_checkbox', None)),
            ('view',
             getattr(self, 'profile_view_show_images_checkbox', None),
             getattr(self, 'profile_view_show_avatars_checkbox', None)),
        )

        for column_name, images_checkbox, avatars_checkbox in column_info:
            if images_checkbox is None or avatars_checkbox is None:
                continue

            images_enabled = bool(images_checkbox.get_active())
            avatars_checkbox.set_sensitive(
                self.profile_function_is_enabled() and images_enabled)

            if not images_enabled and avatars_checkbox.get_active():
                if column_name == 'standard':
                    self.updating_standard_profile_controls = True
                    try:
                        avatars_checkbox.set_active(False)
                    finally:
                        self.updating_standard_profile_controls = False
                    if not hasattr(self, 'standard_profile_save_choices'):
                        self.standard_profile_save_choices = {}
                    self.standard_profile_save_choices[
                        'interface.graphview-show-avatars'] = False
                else:
                    self.updating_view_profile_controls = True
                    try:
                        avatars_checkbox.set_active(False)
                    finally:
                        self.updating_view_profile_controls = False
                    if not hasattr(self, 'view_profile_save_choices'):
                        self.view_profile_save_choices = (
                            self.get_empty_view_profile_save_choices())
                    self.view_profile_save_choices[
                        'interface.graphview-show-avatars'] = False

        return False

    def cb_update_avatars_style(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the avatars setting.
        """
        for widget in self.avatar_widgets:
            widget.set_visible(entry == '0')
        self.graph_widget.populate(self.get_active())

    def cb_on_combo_show(self, combobox):
        """
        Called when the configuration menu show combobox widget for avatars.
        Used to hide custom avatars settings.
        """
        for widget in self.avatar_widgets:
            widget.set_visible(combobox.get_active() == 0)

    def cb_male_avatar_set(self, file_chooser_button):
        """
        Called when the configuration menu changes the male avatar.
        """
        self._config.set('interface.graphview-avatars-male',
                         file_chooser_button.get_filename())
        self.graph_widget.populate(self.get_active())

    def cb_female_avatar_set(self, file_chooser_button):
        """
        Called when the configuration menu changes the female avatar.
        """
        self._config.set('interface.graphview-avatars-female',
                         file_chooser_button.get_filename())
        self.graph_widget.populate(self.get_active())

    def cb_unknown_avatar_set(self, file_chooser_button):
        """
        Called when the configuration menu changes the unknown sex avatar.
        """
        self._config.set('interface.graphview-avatars-unknown',
                         file_chooser_button.get_filename())
        self.graph_widget.populate(self.get_active())

    def cb_other_avatar_set(self, file_chooser_button):
        """
        Called when the configuration menu changes the other sex avatar.
        """
        self._config.set('interface.graphview-avatars-other',
                         file_chooser_button.get_filename())
        self.graph_widget.populate(self.get_active())

    def cb_update_show_full_dates(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the date setting.
        """
        self.show_full_dates = entry == 'True'
        self.graph_widget.populate(self.get_active())

    def cb_update_show_places(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the place setting.
        """
        self.show_places = entry == 'True'
        self.graph_widget.populate(self.get_active())

    def cb_update_place_fmt(self, _client, _cnxn_id, _entry, _data):
        """
        Called when the configuration menu changes the place setting.
        """
        self.graph_widget.populate(self.get_active())

    def cb_update_show_tag_color(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the show tags setting.
        """
        self.show_tag_color = entry == 'True'
        self.graph_widget.populate(self.get_active())

    def cb_update_show_lines(self, _client, _cnxn_id, _entry, _data):
        """
        Called when the configuration menu changes the line setting.
        """
        self.graph_widget.populate(self.get_active())

    def cb_update_highlight_home_person(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the highlight home
        person setting.
        """
        self.highlight_home_person = entry == 'True'
        self.graph_widget.populate(self.get_active())

    def cb_update_home_path_color(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the path person color.
        """
        self.home_path_color = entry
        self.graph_widget.populate(self.get_active())

    def cb_update_desc_generations(self, _client, _cnxd_id, entry, _data):
        """
        Called when the configuration menu changes the descendant generation
        count setting.
        """
        self.descendant_generations = entry
        self.graph_widget.populate(self.get_active())

    def cb_update_ancestor_generations(self, _client, _cnxd_id, entry, _data):
        """
        Called when the configuration menu changes the ancestor generation
        count setting.
        """
        self.ancestor_generations = entry
        self.graph_widget.populate(self.get_active())

    def cb_update_people_limit(self, _client, _cnxd_id, entry, _data):
        self.people_limit = entry
        # 0 means unlimited. The Standard/View profile
        # checkboxes cannot be selected while the live value is 0, although
        # the numeric 0 is still written to every profile JSON.
        self.update_profile_people_limit_controls_sensitivity()
        self.graph_widget.populate(self.get_active())

    def cb_update_show_animation(self, _client, _cnxd_id, entry, _data):
        """
        Called when the configuration menu changes the show animation
        setting.
        """
        if entry == 'True':
            self.graph_widget.animation.show_animation = True
            # enable animate options
            for widget in self.ani_widgets:
                widget.set_sensitive(True)
        else:
            self.graph_widget.animation.show_animation = False
            # diable animate options
            for widget in self.ani_widgets:
                widget.set_sensitive(False)

    def cb_update_animation_count(self, _client, _cnxd_id, entry, _data):
        """
        Called when the configuration menu changes the animation count
        setting.
        """
        self.graph_widget.animation.max_count = int(entry) * 2

    def cb_update_animation_speed(self, _client, _cnxd_id, entry, _data):
        """
        Called when the configuration menu changes the animation speed
        setting.
        """
        self.graph_widget.animation.speed = 50 * int(entry)

    def cb_update_search_all_db(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the search setting.
        """
        value = entry == 'True'
        self.graph_widget.search_widget.set_options(search_all_db=value)

    def cb_update_search_show_images(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the search setting.
        """
        value = entry == 'True'
        self.graph_widget.search_widget.set_options(show_images=value)
        self.graph_widget.show_images_option = value

    def cb_update_search_marked_first(self, _client, _cnxn_id, entry, _data):
        """
        Called when the configuration menu changes the search setting.
        """
        value = entry == 'True'
        self.graph_widget.search_widget.set_options(marked_first=value)

    def cb_update_spacing(self, _client, _cnxd_id, _entry, _data):
        """
        Called when the ranksep or nodesep setting changed.
        """
        self.graph_widget.populate(self.get_active())

    def cb_update_person_theme(self, _client, _cnxd_id, _entry, _data):
        """
        Called when person theme setting changed.
        """
        self.graph_widget.populate(self.get_active())

    def cb_show_all_connected(self, _client, _cnxd_id, _entry, _data):
        """
        Called when show all connected setting changed.
        """
        value = _entry == 'True'
        self.graph_widget.all_connected_btn.set_active(value)
        self.graph_widget.populate(self.get_active())

    def cb_update_family_filter(self, _client, _cnxd_id, _entry, _data):
        """
        Called when family tag filter setting changed.
        """
        if getattr(self, 'updating_family_tag_filter_safety', False):
            return

        value = (_entry is True or _entry == 'True')
        if value and not self.family_tag_filter_value_is_allowed(True):
            self.turn_off_family_tag_filter_for_missing_tag(show_warning=False)
            if self.graph_widget and self.get_active():
                self.graph_widget.populate(self.get_active())
            return

        self.graph_widget.populate(self.get_active())

    def cb_update_active_person_border_size(self, _client, _cnxd_id, entry, _data):
        """
        Called when the active person border size changes
        """
        self.graph_widget.populate(self.get_active())

    def cb_update_person_border_size(self, _client, _cnxd_id, entry, _data):
        """
        Called when the person border size changes
        """
        self.graph_widget.populate(self.get_active())

    def cb_update_direction(self, _client, _cnxn_id, _entry, _data):
        """
        Called when the configuration menu changes the direction setting.
        """
        self.graph_widget.populate(self.get_active())

    def config_change_font(self, font_button):
        """
        Called when font is change.
        """
        font_family = font_button.get_font_family()
        if font_family is not None:
            font_name = font_family.get_name()
        else:
            font_name = ''
        # apply Pango.SCALE=1024 to font size
        font_size = int(font_button.get_font_size() / 1024)
        self._config.set('interface.graphview-font', [font_name, font_size])
        self.graph_widget.retest_font = True
        self.graph_widget.populate(self.get_active())

    def config_connect(self):
        """
        Overwriten from  :class:`~gui.views.pageview.PageView method
        This method will be called after the ini file is initialized,
        use it to monitor changes in the ini file.
        """
        self._config.connect('interface.graphview-show-images',
                             self.cb_update_show_images)
        self._config.connect('interface.graphview-show-id',
                             self.cb_update_show_ID)
        self._config.connect('interface.graphview-show-avatars',
                             self.cb_update_show_avatars)
        self._config.connect('interface.graphview-avatars-style',
                             self.cb_update_avatars_style)
        self._config.connect('interface.graphview-show-full-dates',
                             self.cb_update_show_full_dates)
        self._config.connect('interface.graphview-show-places',
                             self.cb_update_show_places)
        self._config.connect('interface.graphview-place-format',
                             self.cb_update_place_fmt)
        self._config.connect('interface.graphview-show-tags',
                             self.cb_update_show_tag_color)
        self._config.connect('interface.graphview-show-lines',
                             self.cb_update_show_lines)
        self._config.connect('interface.graphview-highlight-home-person',
                             self.cb_update_highlight_home_person)
        self._config.connect('interface.graphview-home-path-color',
                             self.cb_update_home_path_color)
        self._config.connect('interface.graphview-descendant-generations',
                             self.cb_update_desc_generations)
        self._config.connect('interface.graphview-ancestor-generations',
                             self.cb_update_ancestor_generations)
        self._config.connect('interface.graphview-people-limit',
                             self.cb_update_people_limit)
        self._config.connect('interface.graphview-show-animation',
                             self.cb_update_show_animation)
        self._config.connect('interface.graphview-animation-speed',
                             self.cb_update_animation_speed)
        self._config.connect('interface.graphview-animation-count',
                             self.cb_update_animation_count)
        self._config.connect('interface.graphview-search-all-db',
                             self.cb_update_search_all_db)
        self._config.connect('interface.graphview-search-show-images',
                             self.cb_update_search_show_images)
        self._config.connect('interface.graphview-search-marked-first',
                             self.cb_update_search_marked_first)
        self._config.connect('interface.graphview-ranksep',
                             self.cb_update_spacing)
        self._config.connect('interface.graphview-nodesep',
                             self.cb_update_spacing)
        self._config.connect('interface.graphview-person-theme',
                             self.cb_update_person_theme)
        self._config.connect('interface.graphview-show-all-connected',
                             self.cb_show_all_connected)
        self._config.connect('interface.graphview-filter-family-tag',
                             self.cb_update_family_filter)
        self._config.connect('interface.graphview-active-person-border-size',
                             self.cb_update_active_person_border_size)
        self._config.connect('interface.graphview-person-border-size',
                             self.cb_update_person_border_size)
        self._config.connect('interface.graphview-direction',
                             self.cb_update_direction)

    def get_graphview_db_profile_info(self):
        """
        Return the family-tree information useful for Graph View profiles.
        """
        db_name = ''
        media_path = ''
        db_internal_path = ''

        try:
            db_name = self.dbstate.db.get_dbname() or ''
        except Exception:
            db_name = ''

        try:
            media_path = self.dbstate.db.get_mediapath() or ''
        except Exception:
            media_path = ''

        try:
            db_internal_path = self.dbstate.db.path or ''
        except Exception:
            db_internal_path = ''

        return db_name, media_path, db_internal_path

    def graphview_family_tag_exists(self):
        """
        Return True when the open family tree has the required ProfileTag tag.

        The "Show people with the person tag "ProfileTag"" option filters on a fixed person
        tag name. If the tag does not exist, enabling the filter would make
        the graph empty or almost empty.
        """
        try:
            db = self.dbstate.db
            for tag_handle in db.get_tag_handles():
                tag = db.get_tag_from_handle(tag_handle)
                if tag and tag.get_name() == FAMILY_TAG:
                    return True
        except Exception:
            pass

        return False

    def family_tag_filter_value_is_allowed(self, value, show_warning=True):
        """
        Return True if the requested family-tag filter value is safe.
        """
        if not value:
            return True

        if self.graphview_family_tag_exists():
            return True

        if show_warning:
            WarningDialog(
                _('ProfileTag tag not found'),
                _('The ProfileTag filter requires a person tag named '
                  '\"ProfileTag\".'),
                parent=self.uistate.window)

        return False

    def turn_off_family_tag_filter_for_missing_tag(self, show_warning=True):
        """
        Turn off "Show people with the person tag "ProfileTag"" when the ProfileTag tag is missing.

        Returns True when the value was changed. The small guard prevents the
        config callback from starting an extra redraw while we are correcting
        the value.
        """
        if not self._config.get('interface.graphview-filter-family-tag'):
            return False

        if self.graphview_family_tag_exists():
            return False

        if show_warning:
            WarningDialog(
                _('ProfileTag tag not found'),
                _('The ProfileTag filter requires a person tag named '
                  '\"ProfileTag\".'),
                parent=self.uistate.window)

        self.updating_family_tag_filter_safety = True
        try:
            self._config.set('interface.graphview-filter-family-tag', False)

            # ConfigDialog's already visible Layout checkbox
            # does not automatically follow the corrective config write.
            # Clear it immediately so the rejected choice is also removed
            # visually. Popup menu items already clear themselves and are
            # unaffected by this extra synchronization.
            widget = getattr(self, 'open_config_widgets', {}).get(
                'interface.graphview-filter-family-tag')
            if widget is not None:
                try:
                    if widget.get_active():
                        widget.set_active(False)
                except Exception:
                    pass
        finally:
            self.updating_family_tag_filter_safety = False

        return True

    def reset_family_tag_filter_at_book_open(self):
        """
        Clear the shared ProfileTag filter silently for every opened book.

        Manual Layout/popup choices therefore only affect the current open
        book. A Standard or View profile may activate the filter again after
        this reset, including through Apply at startup.
        """
        if not self._config.get('interface.graphview-filter-family-tag'):
            return False

        self.updating_family_tag_filter_safety = True
        try:
            self._config.set('interface.graphview-filter-family-tag', False)

            # A Configure dialog can remain open while changing books.
            # Keep only its ordinary Layout checkbox aligned with the reset.
            widget = getattr(self, 'open_config_widgets', {}).get(
                'interface.graphview-filter-family-tag')
            if widget is not None:
                try:
                    if widget.get_active():
                        widget.set_active(False)
                except Exception:
                    pass
        finally:
            self.updating_family_tag_filter_safety = False

        return True

    def make_safe_profile_filename(self, name):
        """
        Make a safe Windows filename from a Gramps family-tree name.
        """
        if not name:
            name = 'GraphView'

        unsafe_chars = '<>:"/\\|?*'
        safe_name = ''.join('_' if ch in unsafe_chars else ch for ch in name)
        safe_name = safe_name.strip().strip('.')

        if not safe_name:
            safe_name = 'GraphView'

        return safe_name

    def get_standard_profile_filename(self):
        """
        Return filename for the user saved standard profile for this family tree.
        """
        db_name, _media_path, _db_internal_path = self.get_graphview_db_profile_info()
        profiles_dir = os.path.join(os.path.dirname(__file__), 'profiles')
        safe_db_name = self.make_safe_profile_filename(db_name)
        return os.path.join(profiles_dir, '%s__standard.json' % safe_db_name)

    def get_original_settings_backup_filename(self):
        """
        Return filename for the one-time backup of the user's original
        Graph View settings for this family tree.
        """
        db_name, _media_path, _db_internal_path = self.get_graphview_db_profile_info()
        profiles_dir = os.path.join(os.path.dirname(__file__), 'profiles')
        safe_db_name = self.make_safe_profile_filename(db_name)
        return os.path.join(
            profiles_dir, '%s__original_settings_backup.json' % safe_db_name)

    def profile_function_is_enabled(self):
        """
        Return True only when the user has explicitly enabled profiles.
        """
        try:
            return bool(
                self.read_profile_startup_settings().get('profiles_enabled'))
        except Exception:
            return False

    def profile_function_action_allowed(self):
        """
        Return True only when profile actions are allowed. This is the
        code-side guard behind the Profiles-page master checkbox.
        """
        if self.profile_function_is_enabled():
            return True

        self.sync_profile_startup_controls()
        return False

    def register_profile_function_control(self, widget):
        """
        Remember a Profiles-page control that must be locked when the
        profile function is disabled. The master checkbox itself is not
        registered here, so it always remains usable.
        """
        if widget is None:
            return widget

        if not hasattr(self, 'profile_function_controls'):
            self.profile_function_controls = []

        self.profile_function_controls.append(widget)
        return widget

    def update_profile_function_controls_sensitivity(self):
        """
        Lock or unlock all profile controls according to the master checkbox.
        Some controls also depend on whether a profile file actually exists.
        """
        enabled = self.profile_function_is_enabled()
        has_current_view_profile = bool(self.current_view_profile_filename)
        standard_context_ready = self.standard_profile_database_context_ready()
        standard_profile_exists = (
            standard_context_ready and self.standard_graphview_profile_exists())

        for widget in getattr(self, 'profile_function_controls', []):
            try:
                widget.set_sensitive(enabled)
            except Exception:
                pass

        for radio in (
                self.profile_startup_none_radio,
                self.profile_startup_standard_radio,
                self.profile_startup_view_radio):
            if radio is not None:
                radio.set_sensitive(enabled)

        if self.profile_startup_standard_radio is not None:
            self.profile_startup_standard_radio.set_sensitive(
                enabled and standard_profile_exists)
            if (standard_context_ready and
                    not standard_profile_exists and
                    self.profile_startup_standard_radio.get_active() and
                    self.profile_startup_none_radio is not None):
                self.profile_startup_none_radio.set_active(True)

        if self.profile_startup_view_radio is not None:
            # "Current View profile" means the
            # View profile that is currently loaded in this Graph View.
            # A saved startup filename alone must not make this radio
            # selectable when the View column/status is clean. However, this
            # sensitivity update must not change startup_mode to "none":
            # during Gramps startup the JSON-saved View profile may not have
            # been auto-loaded yet. The automatic loader still needs the
            # saved "view" mode and filename.
            self.profile_startup_view_radio.set_sensitive(
                enabled and has_current_view_profile)

        if self.current_view_profile_save_button is not None:
            self.current_view_profile_save_button.set_sensitive(
                enabled and has_current_view_profile)
        if self.current_view_profile_delete_button is not None:
            self.current_view_profile_delete_button.set_sensitive(
                enabled and has_current_view_profile)
        # Load Standard profile is available only when
        # the open family tree actually has a saved Standard profile.
        # The loader itself keeps the same check as a safety net in case
        # the file is removed after the button/menu has been created.
        if self.standard_profile_load_button is not None:
            self.standard_profile_load_button.set_sensitive(
                enabled and standard_profile_exists)
        if self.standard_profile_delete_button is not None:
            self.standard_profile_delete_button.set_sensitive(
                enabled and standard_profile_exists)

        self.update_profile_people_limit_controls_sensitivity()

        # The master switch above enables all registered
        # controls. Reapply the stricter image/avatar dependency afterwards.
        self.update_profile_avatar_controls_sensitivity()

    def get_profile_startup_settings_filename(self):
        """
        Return the small JSON file that stores Graph View profile startup
        settings for this family tree.

        Keep our profile startup choices in the profiles
        folder instead of adding more data to the Gramps ini/config file.
        """
        db_name, _media_path, _db_internal_path = self.get_graphview_db_profile_info()
        profiles_dir = os.path.join(os.path.dirname(__file__), 'profiles')
        safe_db_name = self.make_safe_profile_filename(db_name)
        return os.path.join(profiles_dir, '%s__startup.json' % safe_db_name)

    def get_default_profile_startup_settings(self):
        """
        Return default startup settings for the profile function.
        """
        db_name, media_path, db_internal_path = self.get_graphview_db_profile_info()
        return {
            'settings_version': 1,
            'settings_type': 'graphview_profile_startup',
            'profiles_enabled': False,
            'use_profiles_temporarily': False,
            'startup_mode': 'none',
            'startup_view_profile_filename': '',
            'startup_view_profile_name': '',
            'db_name': db_name,
            'media_path': media_path,
            'db_internal_path': db_internal_path,
        }

    def read_legacy_profile_startup_settings(self):
        """
        Read legacy profile startup values from the Gramps configuration.
        This is only a migration fallback; current values are stored in the
        profile folder's own startup JSON file.
        """
        settings = {}

        try:
            settings['profiles_enabled'] = bool(
                self._config.get('interface.graphview-profiles-enabled'))
        except Exception:
            pass

        try:
            startup_mode = self._config.get(
                'interface.graphview-profile-startup-mode')
            if startup_mode in ('none', 'standard', 'view'):
                settings['startup_mode'] = startup_mode
        except Exception:
            pass

        try:
            filename = self._config.get(
                'interface.graphview-profile-startup-view-filename') or ''
            if isinstance(filename, str):
                settings['startup_view_profile_filename'] = filename
        except Exception:
            pass

        try:
            profile_name = self._config.get(
                'interface.graphview-profile-startup-view-name') or ''
            if isinstance(profile_name, str):
                settings['startup_view_profile_name'] = profile_name
        except Exception:
            pass

        return settings

    def read_profile_startup_settings(self):
        """
        Read profile startup settings from our own JSON file.
        """
        settings = self.get_default_profile_startup_settings()
        filename = self.get_profile_startup_settings_filename()

        loaded_from_legacy = False
        try:
            with open(filename, 'r', encoding='utf-8') as json_file:
                loaded_settings = json.load(json_file)
        except (OSError, json.JSONDecodeError):
            loaded_settings = self.read_legacy_profile_startup_settings()
            loaded_from_legacy = bool(loaded_settings)

        if isinstance(loaded_settings, dict):
            for key in (
                    'profiles_enabled',
                    'use_profiles_temporarily',
                    'startup_mode',
                    'startup_view_profile_filename',
                    'startup_view_profile_name'):
                if key in loaded_settings:
                    settings[key] = loaded_settings[key]

        settings['profiles_enabled'] = bool(settings.get('profiles_enabled'))
        settings['use_profiles_temporarily'] = bool(
            settings.get('use_profiles_temporarily'))

        startup_mode = settings.get('startup_mode')
        if startup_mode not in ('none', 'standard', 'view'):
            settings['startup_mode'] = 'none'

        for key in ('startup_view_profile_filename', 'startup_view_profile_name'):
            if not isinstance(settings.get(key), str):
                settings[key] = ''

        # If a legacy version saved startup values in Gramps config, copy
        # them once to the profile folder's own JSON file. From then on this
        # code reads/writes that JSON file and leaves Gramps ini alone.
        if loaded_from_legacy:
            try:
                settings['updated_at'] = datetime.now().isoformat(
                    timespec="seconds")
                os.makedirs(os.path.dirname(filename), exist_ok=True)
                with open(filename, 'w', encoding='utf-8') as json_file:
                    json.dump(settings, json_file, ensure_ascii=False, indent=2)
            except OSError:
                pass

        return settings

    def write_profile_startup_settings(self, updates):
        """
        Update our own profile startup JSON file.
        """
        settings = self.read_profile_startup_settings()
        if isinstance(updates, dict):
            settings.update(updates)

        db_name, media_path, db_internal_path = self.get_graphview_db_profile_info()
        settings['settings_version'] = 1
        settings['settings_type'] = 'graphview_profile_startup'
        settings['db_name'] = db_name
        settings['media_path'] = media_path
        settings['db_internal_path'] = db_internal_path
        settings['updated_at'] = datetime.now().isoformat(timespec="seconds")

        if settings.get('startup_mode') not in ('none', 'standard', 'view'):
            settings['startup_mode'] = 'none'

        settings['profiles_enabled'] = bool(settings.get('profiles_enabled'))
        settings['use_profiles_temporarily'] = bool(
            settings.get('use_profiles_temporarily'))

        filename = self.get_profile_startup_settings_filename()
        try:
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            with open(filename, 'w', encoding='utf-8') as json_file:
                json.dump(settings, json_file, ensure_ascii=False, indent=2)
        except OSError as msg:
            WarningDialog(
                _('Could not save Graph View startup settings'),
                str(msg),
                parent=self.uistate.window)
            return False

        return True

    def set_profile_function_enabled(self, enabled):
        """
        Save whether the profile function is enabled in startup JSON.
        """
        updates = {'profiles_enabled': bool(enabled)}
        if not enabled:
            updates.update({
                'use_profiles_temporarily': False,
                'startup_mode': 'none',
                'startup_view_profile_filename': '',
                'startup_view_profile_name': '',
            })
        result = self.write_profile_startup_settings(updates)
        if result:
            self.update_temporary_profile_restore_enabled_for_open_book()
        return result

    def profiles_temporary_is_enabled(self):
        """
        Return True when loaded profiles should be used temporarily.

        When used together with Enable profile function, the book-opening
        GraphView settings are restored when the book is closed. A snapshot
        failure may force this off for the current open book even when an old
        startup JSON value could not be rewritten.
        """
        if getattr(
                self,
                'temporary_profile_restore_forced_off_for_open_book',
                False):
            return False

        try:
            return bool(
                self.read_profile_startup_settings().get(
                    'use_profiles_temporarily'))
        except Exception:
            return False

    def set_profiles_temporary_enabled(self, enabled):
        """
        Save whether profile loads should be treated as temporary.
        """
        result = self.write_profile_startup_settings(
            {'use_profiles_temporarily': bool(enabled)})
        if result:
            self.update_temporary_profile_restore_enabled_for_open_book()
        return result

    def temporary_profile_restore_snapshot_is_valid(self):
        """Return True for this session's readable temporary snapshot."""
        if not getattr(
                self, 'temporary_profile_restore_snapshot_created', False):
            return False

        filename = getattr(
            self, 'temporary_profile_restore_snapshot_filename', '')
        if not filename or not os.path.isfile(filename):
            return False

        try:
            with open(filename, 'r', encoding='utf-8') as json_file:
                profile = json.load(json_file)
        except (OSError, json.JSONDecodeError):
            return False

        return bool(
            isinstance(profile, dict) and
            profile.get('settings_type') ==
            'graphview_temporary_profile_restore')

    def ask_create_temporary_profile_restore_snapshot_now(self):
        """
        Let the user choose whether the current settings should become the
        restore point when the book-opening snapshot is unavailable.
        """
        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Create temporary restore point?'))
        dialog.format_secondary_text(
            _('The Graph View settings from when the family tree was opened '
              'are not available. You can save the current Graph View '
              'settings as the restore point now, or cancel temporary use.\n\n'
              'Any changes made since the family tree was opened will be '
              'included in the new restore point.'))
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(
            _('Save current settings'), Gtk.ResponseType.OK)
        response = dialog.run()
        dialog.destroy()
        return response == Gtk.ResponseType.OK

    def force_profiles_temporary_off_for_open_book(self, show_warning=False):
        """
        Disable temporary use for this book without blocking profile loading.

        The in-memory guard remains effective even if the startup JSON cannot
        be rewritten because the same folder is unavailable.
        """
        error_text = getattr(
            self, 'temporary_profile_restore_snapshot_last_error', '')

        self.temporary_profile_restore_forced_off_for_open_book = True
        self.temporary_profile_restore_enabled_for_open_book = False
        self.set_profiles_temporary_enabled(False)
        self.sync_profile_startup_controls()

        if show_warning:
            message = _(
                'The Graph View settings needed for temporary use could not '
                'be saved. "Use profiles temporarily" has been turned off '
                'for this family tree. Profiles will still load normally, '
                'but these settings cannot be restored when the family tree '
                'is closed.')
            if error_text:
                message += '\n\n' + error_text
            WarningDialog(
                _('Temporary profile use disabled'),
                message,
                parent=self.uistate.window)

    def cb_profiles_temporary_toggled(self, checkbutton):
        """Save or safely reject the temporary-profile checkbox choice."""
        if getattr(self, 'updating_profile_startup_controls', False):
            return

        if not self.profile_function_action_allowed():
            return

        requested = bool(checkbutton.get_active())
        if not requested:
            self.temporary_profile_restore_forced_off_for_open_book = False
            self.set_profiles_temporary_enabled(False)
            self.update_profile_function_controls_sensitivity()
            return

        if self.temporary_profile_restore_snapshot_is_valid():
            self.temporary_profile_restore_forced_off_for_open_book = False
            self.set_profiles_temporary_enabled(True)
            self.update_profile_function_controls_sensitivity()
            return

        if not self.ask_create_temporary_profile_restore_snapshot_now():
            # Keep the current book safely off even if writing the startup
            # preference is impossible for the same filesystem reason.
            self.temporary_profile_restore_forced_off_for_open_book = True
            self.temporary_profile_restore_enabled_for_open_book = False
            self.set_profiles_temporary_enabled(False)
            self.sync_profile_startup_controls()
            self.update_profile_function_controls_sensitivity()
            return

        # The user knowingly chooses the current settings as the restore point.
        # Keep the forced-off guard during the write; clear it only on success.
        if self.create_temporary_profile_restore_snapshot(
                force=True, warn_on_error=False):
            self.temporary_profile_restore_forced_off_for_open_book = False
            if not self.set_profiles_temporary_enabled(True):
                self.temporary_profile_restore_forced_off_for_open_book = True
                self.temporary_profile_restore_enabled_for_open_book = False
            self.sync_profile_startup_controls()
        else:
            self.force_profiles_temporary_off_for_open_book(
                show_warning=True)

        self.update_profile_function_controls_sensitivity()

    def get_temporary_profile_restore_filename(self):
        """
        Return filename for the temporary restore snapshot for this family tree.
        """
        db_name, _media_path, _db_internal_path = self.get_graphview_db_profile_info()
        profiles_dir = os.path.join(os.path.dirname(__file__), 'profiles')
        safe_db_name = self.make_safe_profile_filename(db_name)
        return os.path.join(
            profiles_dir, '%s__temporary_profile_restore.json' % safe_db_name)

    def build_temporary_profile_restore_data(self):
        """
        Build a snapshot of the current shared GraphView settings.

        This is the state we may later restore when profiles are used
        temporarily. It must be captured before a Standard/View profile changes
        the shared GraphView config values.
        """
        db_name, media_path, db_internal_path = self.get_graphview_db_profile_info()

        def get_config_value(config_key):
            return self._config.get(config_key)

        profile = {
            'settings_version': 1,
            'settings_type': 'graphview_temporary_profile_restore',
            'restore_active': True,
            'created_at': datetime.now().isoformat(timespec='seconds'),
            'db_name': db_name,
            'media_path': media_path,
            'db_internal_path': db_internal_path,
            'content': {
                'interface.graphview-ancestor-generations': get_config_value(
                    'interface.graphview-ancestor-generations'),
                'interface.graphview-descendant-generations': get_config_value(
                    'interface.graphview-descendant-generations'),
                'interface.graphview-show-all-connected': get_config_value(
                    'interface.graphview-show-all-connected'),
                'interface.graphview-people-limit': get_config_value(
                    'interface.graphview-people-limit'),
            },
            'layout': {
                'interface.graphview-direction': get_config_value(
                    'interface.graphview-direction'),
                'interface.graphview-show-lines': get_config_value(
                    'interface.graphview-show-lines'),
                'interface.graphview-ranksep': get_config_value(
                    'interface.graphview-ranksep'),
                'interface.graphview-nodesep': get_config_value(
                    'interface.graphview-nodesep'),
            },
            'display': {
                'interface.graphview-show-images': get_config_value(
                    'interface.graphview-show-images'),
                'interface.graphview-show-id': get_config_value(
                    'interface.graphview-show-id'),
                'interface.graphview-show-avatars': get_config_value(
                    'interface.graphview-show-avatars'),
                'interface.graphview-show-full-dates': get_config_value(
                    'interface.graphview-show-full-dates'),
                'interface.graphview-show-places': get_config_value(
                    'interface.graphview-show-places'),
                'interface.graphview-place-format': get_config_value(
                    'interface.graphview-place-format'),
                'interface.graphview-show-tags': get_config_value(
                    'interface.graphview-show-tags'),
                'interface.graphview-filter-family-tag': get_config_value(
                    'interface.graphview-filter-family-tag'),
            },
            'style': {
                'interface.graphview-highlight-home-person': get_config_value(
                    'interface.graphview-highlight-home-person'),
                'interface.graphview-home-path-color': get_config_value(
                    'interface.graphview-home-path-color'),
                'interface.graphview-person-theme': get_config_value(
                    'interface.graphview-person-theme'),
                'interface.graphview-font': get_config_value(
                    'interface.graphview-font'),
                'interface.graphview-avatars-style': get_config_value(
                    'interface.graphview-avatars-style'),
                'interface.graphview-person-border-size': get_config_value(
                    'interface.graphview-person-border-size'),
                'interface.graphview-active-person-border-size': get_config_value(
                    'interface.graphview-active-person-border-size'),
                'interface.graphview-avatars-male': get_config_value(
                    'interface.graphview-avatars-male'),
                'interface.graphview-avatars-female': get_config_value(
                    'interface.graphview-avatars-female'),
                'interface.graphview-avatars-unknown': get_config_value(
                    'interface.graphview-avatars-unknown'),
                'interface.graphview-avatars-other': get_config_value(
                    'interface.graphview-avatars-other'),
            },
        }

        if self.graph_widget:
            try:
                profile['view_state_optional'] = {
                    'interface.graphview-scale': self.graph_widget.scale,
                    'horizontal_adjustment_value': (
                        self.graph_widget.hadjustment.get_value()),
                    'vertical_adjustment_value': (
                        self.graph_widget.vadjustment.get_value()),
                }
            except Exception:
                pass

        return profile

    def temporary_profile_restore_context_ready(self):
        """
        Return True when the open book has enough identity for a safe
        temporary restore filename.
        """
        db_name, _media_path, db_internal_path = (
            self.get_graphview_db_profile_info())
        return bool(db_name and db_internal_path)

    def create_temporary_profile_restore_snapshot(self, force=False,
                                                  warn_on_error=True):
        """
        Save the current shared GraphView settings.

        The snapshot is created as early as possible for every opened book,
        regardless of profile settings. It is restored on close only when both
        profile controls request that behavior.
        Within one GraphView session the snapshot is written once, unless
        force=True is used for a new book/opening.
        """
        if (self.temporary_profile_restore_snapshot_created and not force):
            return True

        self.temporary_profile_restore_snapshot_last_error = ''

        if not self.temporary_profile_restore_context_ready():
            return False

        filename = self.get_temporary_profile_restore_filename()
        profile = self.build_temporary_profile_restore_data()

        temp_filename = ''
        try:
            directory = os.path.dirname(filename)
            os.makedirs(directory, exist_ok=True)

            # Write the complete snapshot beside the real file
            # first. os.replace() then switches files atomically, so a failed
            # write cannot leave the previous valid snapshot empty or partial.
            with tempfile.NamedTemporaryFile(
                    mode='w', encoding='utf-8', dir=directory,
                    prefix=os.path.basename(filename) + '.', suffix='.tmp',
                    delete=False) as json_file:
                temp_filename = json_file.name
                json.dump(profile, json_file, ensure_ascii=False, indent=2)
                json_file.flush()
                os.fsync(json_file.fileno())

            os.replace(temp_filename, filename)
            temp_filename = ''
        except (OSError, TypeError, ValueError) as msg:
            if temp_filename:
                try:
                    os.remove(temp_filename)
                except OSError:
                    pass

            self.temporary_profile_restore_snapshot_last_error = str(msg)
            if warn_on_error:
                WarningDialog(
                    _('Could not save temporary Graph View settings'),
                    str(msg),
                    parent=self.uistate.window)
            return False

        self.temporary_profile_restore_snapshot_last_error = ''
        self.temporary_profile_restore_snapshot_created = True
        self.temporary_profile_restore_snapshot_filename = filename
        self.temporary_profile_restore_restored = False
        self.update_temporary_profile_restore_enabled_for_open_book()
        return True

    def create_temporary_profile_restore_snapshot_at_book_open(self,
                                                               force=False):
        """
        Try to capture the opening settings without blocking normal startup.

        A real write error disables temporary use with one warning when that
        option was enabled. An early not-ready database context is retried
        later and is not treated as a file error.
        """
        created = self.create_temporary_profile_restore_snapshot(
            force=force, warn_on_error=False)
        if (not created and
                self.temporary_profile_restore_snapshot_last_error and
                self.profiles_temporary_is_enabled()):
            self.force_profiles_temporary_off_for_open_book(
                show_warning=True)
        return created

    def prepare_temporary_profile_restore_snapshot_before_load(self):
        """
        Try once more before a profile changes settings.

        Failure never rejects the profile. Temporary use is disabled and the
        graph/profile continues normally.
        """
        created = self.create_temporary_profile_restore_snapshot(
            warn_on_error=False)
        if not created and self.profiles_temporary_is_enabled():
            self.force_profiles_temporary_off_for_open_book(
                show_warning=True)
        return created

    def update_temporary_profile_restore_enabled_for_open_book(self):
        """
        Remember whether the currently open book should restore the temp
        GraphView snapshot when it closes.

        This cached value is important because Gramps may already be changing
        database context when close/switch callbacks run. The checkbox values
        are still stored in the startup JSON; this value only protects the
        close-time decision for the currently open book.
        """
        try:
            self.temporary_profile_restore_enabled_for_open_book = bool(
                self.profile_function_is_enabled() and
                self.profiles_temporary_is_enabled())
        except Exception:
            pass

        return self.temporary_profile_restore_enabled_for_open_book

    def restore_temporary_profile_settings_on_close(self):
        """
        Restore the book-opening GraphView settings before the book/view closes.

        Restoration occurs only when both user controls are enabled:
        Enable profile function + Use profiles temporarily. The snapshot is
        otherwise left alone, so Gramps keeps its normal shared settings.
        """
        if getattr(self, 'temporary_profile_restore_restored', False):
            return False

        if not getattr(self, 'temporary_profile_restore_enabled_for_open_book', False):
            # If the cached state was never initialized but context is still
            # valid, give the current book settings one final chance.
            if not self.update_temporary_profile_restore_enabled_for_open_book():
                return False

        filename = getattr(
            self, 'temporary_profile_restore_snapshot_filename', '')
        if not filename:
            try:
                filename = self.get_temporary_profile_restore_filename()
            except Exception:
                filename = ''

        if not filename or not os.path.isfile(filename):
            return False

        try:
            with open(filename, 'r', encoding='utf-8') as json_file:
                profile = json.load(json_file)
        except (OSError, json.JSONDecodeError):
            return False

        if not isinstance(profile, dict):
            return False

        if profile.get('settings_type') != 'graphview_temporary_profile_restore':
            return False

        if not self.restore_temporary_profile_restore_data(profile):
            return False

        self.temporary_profile_restore_restored = True
        return True

    @batch_profile_graph_refresh(redraw_after=False)
    def restore_temporary_profile_restore_data(self, profile):
        """
        Apply a saved temporary restore snapshot back to shared GraphView config.
        """
        allowed_config_keys = [
            'interface.graphview-direction',
            'interface.graphview-show-lines',
            'interface.graphview-ranksep',
            'interface.graphview-nodesep',
            'interface.graphview-ancestor-generations',
            'interface.graphview-descendant-generations',
            'interface.graphview-show-all-connected',
            'interface.graphview-people-limit',
            'interface.graphview-show-images',
            'interface.graphview-show-id',
            'interface.graphview-show-avatars',
            'interface.graphview-show-full-dates',
            'interface.graphview-show-places',
            'interface.graphview-place-format',
            'interface.graphview-show-tags',
            'interface.graphview-filter-family-tag',
            'interface.graphview-highlight-home-person',
            'interface.graphview-home-path-color',
            'interface.graphview-person-theme',
            'interface.graphview-font',
            'interface.graphview-avatars-style',
            'interface.graphview-person-border-size',
            'interface.graphview-active-person-border-size',
            'interface.graphview-avatars-male',
            'interface.graphview-avatars-female',
            'interface.graphview-avatars-unknown',
            'interface.graphview-avatars-other',
        ]

        restored_values = {}
        for section_name in ('content', 'layout', 'display', 'style'):
            section = profile.get(section_name, {})
            if isinstance(section, dict):
                restored_values.update(section)

        if (restored_values.get('interface.graphview-filter-family-tag') and
                not self.family_tag_filter_value_is_allowed(
                    True, show_warning=False)):
            restored_values['interface.graphview-filter-family-tag'] = False

        try:
            # Generations and Spacings are controlled by
            # toolbar spin buttons that save through a short GLib timeout.
            # Cancel any still-pending spinner write before restoring the
            # snapshot, otherwise it can write an old profile value back
            # after the correct temp value has been restored.
            if (self.graph_widget is not None and
                    hasattr(self.graph_widget,
                            'cancel_pending_spinner_update')):
                self.graph_widget.cancel_pending_spinner_update()

            self.set_profile_config_values_all_connected_last(
                allowed_config_keys, restored_values)

            # The four toolbar spinners do not follow config changes by
            # themselves. Keep their visible values aligned with the temp
            # snapshot, just as an ordinary Standard/View profile load does.
            if (self.graph_widget is not None and
                    hasattr(self.graph_widget, 'sync_profile_controls')):
                self.graph_widget.sync_profile_controls()

            view_state = profile.get('view_state_optional', {})
            if isinstance(view_state, dict):
                if 'interface.graphview-scale' in view_state:
                    scale = view_state.get('interface.graphview-scale')
                    self._config.set('interface.graphview-scale', scale)
                    if self.graph_widget is not None:
                        self.graph_widget.scale = scale

                if self.graph_widget is not None:
                    if 'horizontal_adjustment_value' in view_state:
                        self.graph_widget.hadjustment.set_value(
                            view_state.get('horizontal_adjustment_value'))
                    if 'vertical_adjustment_value' in view_state:
                        self.graph_widget.vadjustment.set_value(
                            view_state.get('vertical_adjustment_value'))
        except Exception:
            return False

        return True

    def get_profile_startup_mode(self):
        """
        Return saved startup mode for the profile function.
        """
        return self.read_profile_startup_settings().get('startup_mode', 'none')

    def set_profile_startup_mode(self, startup_mode):
        """
        Save startup mode in our own startup JSON file.
        """
        if startup_mode not in ('none', 'standard', 'view'):
            startup_mode = 'none'
        return self.write_profile_startup_settings(
            {'startup_mode': startup_mode})

    def get_startup_view_profile_filename(self):
        """
        Return the View-profile JSON filename saved for startup.
        """
        return self.read_profile_startup_settings().get(
            'startup_view_profile_filename', '')

    def get_startup_view_profile_name(self):
        """
        Return the saved display name for the startup View profile.
        """
        settings = self.read_profile_startup_settings()
        profile_name = settings.get('startup_view_profile_name', '')

        if not profile_name:
            filename = settings.get('startup_view_profile_filename', '')
            if filename:
                profile_name = os.path.splitext(os.path.basename(filename))[0]

        return profile_name

    def remember_startup_view_profile(self, filename, profile_name=None):
        """
        Remember which View-profile JSON file should be used at startup.
        """
        if not filename:
            return False

        if profile_name is None:
            profile_name = os.path.splitext(os.path.basename(filename))[0]

        return self.write_profile_startup_settings({
            'startup_view_profile_filename': filename,
            'startup_view_profile_name': profile_name or '',
        })

    def clear_startup_view_profile(self):
        """
        Forget the saved startup View-profile JSON file.
        """
        return self.write_profile_startup_settings({
            'startup_view_profile_filename': '',
            'startup_view_profile_name': '',
        })

    def graphview_people_limit_is_real_limit(self, value):
        """
        Return True only when Limit number displayed is actually a limit.

        In Graph View, 0 means unlimited. For profile include/exclude
        checkboxes that should be treated as not having a limit selected.
        Only values greater than 0 count as a selected
        limit. 0, negative values, empty values and invalid values do not.
        """
        try:
            return int(value) > 0
        except (TypeError, ValueError):
            return False

    def get_profile_people_limit_choice(self, profile, default_value=False):
        """
        Return whether a positive people limit is selected for profile load.

        The numeric value is stored in every Standard/View profile,
        including 0. A separate top-level profile_choices flag preserves the
        include/exclude checkbox for positive limits. Older profiles without
        this flag retain the former key-presence behavior.
        """
        if not isinstance(profile, dict):
            return bool(default_value)

        content = profile.get('content', {})
        if not isinstance(content, dict):
            return False

        key = 'interface.graphview-people-limit'
        if key not in content:
            return False

        value = content.get(key)
        if not self.graphview_people_limit_is_real_limit(value):
            return False

        choices = profile.get('profile_choices', {})
        if isinstance(choices, dict) and 'people_limit' in choices:
            return bool(choices.get('people_limit'))

        # Backward compatibility: in older profiles, a positive value was
        # present only when the checkbox had been selected.
        return True

    def set_profile_people_limit_choice(self, profile, selected, value=None):
        """Always store the value and remember the positive-limit choice."""
        if not isinstance(profile, dict):
            return profile

        if value is None:
            value = self._config.get('interface.graphview-people-limit')

        content = profile.get('content')
        if not isinstance(content, dict):
            content = {}
            profile['content'] = content
        content['interface.graphview-people-limit'] = value

        choices = profile.get('profile_choices')
        if not isinstance(choices, dict):
            choices = {}
            profile['profile_choices'] = choices
        choices['people_limit'] = bool(
            selected and self.graphview_people_limit_is_real_limit(value))
        return profile

    def apply_profile_people_limit_load_rule(self, profile, loaded_values):
        """
        Apply the people-limit load rule to an already collected config dictionary.

        A saved 0 always loads because it means unlimited. A positive value
        loads only when its profile checkbox was selected.
        """
        if not isinstance(profile, dict) or not isinstance(loaded_values, dict):
            return

        key = 'interface.graphview-people-limit'
        if key not in loaded_values:
            return

        value = loaded_values.get(key)
        if self.graphview_people_limit_is_real_limit(value):
            if not self.get_profile_people_limit_choice(profile):
                loaded_values.pop(key, None)
        else:
            # The supported non-positive value is 0 = unlimited. Keep it so
            # loading this profile can remove a previously active limit.
            try:
                if int(value) != 0:
                    loaded_values.pop(key, None)
            except (TypeError, ValueError):
                loaded_values.pop(key, None)

    def update_profile_people_limit_controls_sensitivity(self):
        """Lock both profile checkboxes while the current value is 0."""
        try:
            selectable = self.graphview_people_limit_is_real_limit(
                self._config.get('interface.graphview-people-limit'))
        except Exception:
            selectable = False

        enabled = self.profile_function_is_enabled()

        standard_check = getattr(
            self, 'profile_standard_people_limit_checkbox', None)
        if standard_check is not None:
            if not selectable:
                self.updating_standard_profile_controls = True
                try:
                    standard_check.set_active(False)
                finally:
                    self.updating_standard_profile_controls = False
                if not hasattr(self, 'standard_profile_group_choices'):
                    self.standard_profile_group_choices = {}
                self.standard_profile_group_choices['people_limit'] = False
            standard_check.set_sensitive(enabled and selectable)

        view_check = getattr(self, 'profile_view_people_limit_checkbox', None)
        if view_check is not None:
            if not selectable:
                self.updating_view_profile_controls = True
                try:
                    view_check.set_active(False)
                finally:
                    self.updating_view_profile_controls = False
                if not hasattr(self, 'view_profile_save_choices'):
                    self.view_profile_save_choices = (
                        self.get_empty_view_profile_save_choices())
                self.view_profile_save_choices['people_limit'] = False
            view_check.set_sensitive(enabled and selectable)

    def build_original_settings_backup_profile_data(self):
        """
        Build a complete View-style backup of the current Graph View.

        The original-settings backup is an exact safety snapshot,
        not a Standard profile. It therefore includes every supported setting,
        Home person, Active person, zoom and chart position. The file is still
        created only once and is never overwritten.
        """
        profile = self.build_full_current_standard_profile_data()
        profile['profile_type'] = 'view_profile'

        active_handle = self.get_active() or ''
        active_person = None
        if active_handle:
            try:
                active_person = self.dbstate.db.get_person_from_handle(
                    active_handle)
            except Exception:
                active_person = None

        home_person = self.dbstate.db.get_default_person()
        home_handle = home_person.get_handle() if home_person else ''

        if active_person:
            profile['active_person'] = {
                'handle': active_handle,
                'gramps_id': active_person.get_gramps_id(),
                'name': displayer.display(active_person),
            }

        if home_person:
            profile['home_person'] = {
                'handle': home_handle,
                'gramps_id': home_person.get_gramps_id(),
                'name': displayer.display(home_person),
            }

        profile['backup_type'] = 'original_graphview_settings'
        profile['backup_note'] = (
            'Created once when the Graph View profile function was enabled.')
        return profile

    def create_original_settings_backup_if_missing(self):
        """
        Create the original-settings backup once. Existing backup files are
        deliberately left untouched.
        """
        filename = self.get_original_settings_backup_filename()

        if os.path.isfile(filename):
            return filename

        profile = self.build_original_settings_backup_profile_data()
        profile['profile_name'] = os.path.splitext(os.path.basename(filename))[0]

        try:
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            with open(filename, 'w', encoding='utf-8') as json_file:
                json.dump(profile, json_file, ensure_ascii=False, indent=2)
        except OSError as msg:
            ErrorDialog(
                _('Could not save Graph View settings backup'),
                str(msg),
                parent=self.uistate.window)
            return ''

        return filename

    def copy_backup_to_first_standard_profile(self, backup_filename):
        """
        Copy the original-settings backup to the first Standard profile.
        An existing Standard profile is not overwritten automatically.
        """
        standard_filename = self.get_standard_profile_filename()

        if os.path.isfile(standard_filename):
            return True

        try:
            with open(backup_filename, 'r', encoding='utf-8') as json_file:
                profile = json.load(json_file)
        except (OSError, json.JSONDecodeError) as msg:
            ErrorDialog(
                _('Could not read Graph View settings backup'),
                str(msg),
                parent=self.uistate.window)
            return False

        profile['profile_name'] = os.path.splitext(
            os.path.basename(standard_filename))[0]
        profile['profile_type'] = 'standard_profile'
        profile['created_at'] = datetime.now().isoformat(timespec="seconds")
        profile['created_from_backup'] = os.path.basename(backup_filename)

        # The first Standard profile should not control
        # Zoom & chart position. Gramps starts by showing the home person,
        # and the profile function must not override that unless the user
        # explicitly saves such a choice later.
        profile.pop('view_state_optional', None)

        # Keep Limit number displayed in the first
        # Standard profile even when it is 0 (unlimited). The checkbox is
        # recorded separately and is false for 0.
        content = profile.get('content', {})
        if not isinstance(content, dict):
            content = {}
            profile['content'] = content
        limit_value = content.get(
            'interface.graphview-people-limit',
            self._config.get('interface.graphview-people-limit'))
        self.set_profile_people_limit_choice(
            profile, self.graphview_people_limit_is_real_limit(limit_value),
            limit_value)

        try:
            os.makedirs(os.path.dirname(standard_filename), exist_ok=True)
            with open(standard_filename, 'w', encoding='utf-8') as json_file:
                json.dump(profile, json_file, ensure_ascii=False, indent=2)
        except OSError as msg:
            ErrorDialog(
                _('Could not create Graph View standard profile'),
                str(msg),
                parent=self.uistate.window)
            return False

        return True

    def clean_first_standard_profile_if_created_from_backup(self):
        """
        Clean the automatically created first Standard profile.

        This is deliberately limited to profiles marked with
        created_from_backup, so later user-saved Standard profiles are not
        silently changed.
        """
        filename = self.get_standard_profile_filename()
        if not os.path.isfile(filename):
            return False

        try:
            with open(filename, 'r', encoding='utf-8') as json_file:
                profile = json.load(json_file)
        except (OSError, json.JSONDecodeError):
            return False

        if not isinstance(profile, dict):
            return False

        if not profile.get('created_from_backup'):
            return False

        changed = False

        if 'view_state_optional' in profile:
            profile.pop('view_state_optional', None)
            changed = True

        content = profile.get('content')
        if not isinstance(content, dict):
            content = {}
            profile['content'] = content
            changed = True

        limit_key = 'interface.graphview-people-limit'
        if limit_key not in content:
            # Migrate early Standard profiles created by development versions, which
            # deliberately removed 0 from the JSON. Prefer the original
            # backup value and fall back to the current GraphView config.
            limit_value = None
            try:
                backup_filename = self.get_original_settings_backup_filename()
                with open(backup_filename, 'r', encoding='utf-8') as json_file:
                    backup_profile = json.load(json_file)
                backup_content = backup_profile.get('content', {})
                if isinstance(backup_content, dict):
                    limit_value = backup_content.get(limit_key)
            except (OSError, json.JSONDecodeError, AttributeError):
                pass
            if limit_value is None:
                limit_value = self._config.get(limit_key)
            content[limit_key] = limit_value
            changed = True

        limit_value = content.get(limit_key)
        choices = profile.get('profile_choices')
        if not isinstance(choices, dict):
            choices = {}
            profile['profile_choices'] = choices
            changed = True
        expected_choice = self.graphview_people_limit_is_real_limit(limit_value)
        if choices.get('people_limit') != expected_choice:
            choices['people_limit'] = expected_choice
            changed = True

        if not changed:
            return False

        try:
            with open(filename, 'w', encoding='utf-8') as json_file:
                json.dump(profile, json_file, ensure_ascii=False, indent=2)
        except OSError:
            return False

        return True

    def enable_profile_function(self):
        """
        Turn on profiles after creating the one-time original-settings backup.

        Enabling the function no longer creates a Standard
        profile. Standard and View columns start empty until the user saves or
        loads a profile explicitly.
        """
        backup_filename = self.create_original_settings_backup_if_missing()
        if not backup_filename:
            return False

        if not self.set_profile_function_enabled(True):
            return False

        self.standard_profile_controls_active = False
        self.set_current_view_profile('', '')
        self.clear_standard_profile_controls()
        self.clear_view_profile_controls()
        self.sync_profile_startup_controls()
        self.update_profile_function_controls_sensitivity()
        self.update_profiles_status_labels()
        self.clear_profiles_page_unsaved()
        return True

    def ask_restore_backup_before_disabling_profiles(self):
        """
        Ask whether to restore the original-settings backup before disabling
        the profile function.
        """
        backup_filename = self.get_original_settings_backup_filename()
        has_backup = os.path.isfile(backup_filename)

        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Disable profile function?'))

        if has_backup:
            dialog.format_secondary_text(
                _('Restore the original Graph View settings backup first?'))
            dialog.add_button(_('Restore backup'), 1)
        else:
            dialog.format_secondary_text(
                _('No original Graph View settings backup was found.'))

        dialog.add_button(_('Disable without restore'), 2)
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)

        response = dialog.run()
        dialog.destroy()
        return response

    def restore_original_settings_backup_profile(self, profile):
        """Restore the internal one-time backup without making it a profile."""
        if not isinstance(profile, dict):
            return False

        if profile.get('profile_version') != 1:
            return False

        # Current original-settings backups are complete View snapshots.
        if profile.get('profile_type') != 'view_profile':
            return False

        home_data = profile.get('home_person', {})
        if isinstance(home_data, dict) and home_data:
            home_handle, home_person = (
                self.resolve_graphview_profile_person_data(home_data))
            if home_person:
                self.dbstate.db.set_default_person_handle(home_handle)

        active_data = profile.get('active_person', {})
        if isinstance(active_data, dict) and active_data:
            active_handle, active_person = (
                self.resolve_graphview_profile_person_data(active_data))
            if active_person:
                self.change_active(active_handle)

        # Reuse the proven Standard apply path for all config values and the
        # optional zoom/chart position, but do not register this internal file
        # as the current View profile.
        settings_profile = dict(profile)
        settings_profile['profile_type'] = 'standard_profile'
        return self.apply_standard_graphview_profile(settings_profile)

    def disable_profile_function(self):
        """
        Turn off profiles, optionally restoring the original-settings backup.
        """
        response = self.ask_restore_backup_before_disabling_profiles()

        if response not in (1, 2):
            return False

        if response == 1:
            backup_filename = self.get_original_settings_backup_filename()
            try:
                with open(backup_filename, 'r', encoding='utf-8') as json_file:
                    profile = json.load(json_file)
            except (OSError, json.JSONDecodeError) as msg:
                ErrorDialog(
                    _('Could not restore Graph View settings backup'),
                    str(msg),
                    parent=self.uistate.window)
                return False

            if not self.restore_original_settings_backup_profile(profile):
                WarningDialog(
                    _('Could not restore Graph View settings backup'),
                    _('The backup could not be applied to this family tree.'),
                    parent=self.uistate.window)
                return False

        if not self.set_profile_function_enabled(False):
            return False

        self.standard_profile_auto_checked = True
        self.standard_profile_auto_scheduled = False

        # Disabling the master function clears both visible
        # profile columns and forgets the current View profile for this
        # session. Saved Standard/View profile files are not deleted.
        self.standard_profile_controls_active = False
        self.set_current_view_profile('', '')
        self.clear_standard_profile_controls()
        self.clear_view_profile_controls()
        self.sync_profile_startup_controls()
        self.update_profile_function_controls_sensitivity()
        self.update_profiles_status_labels()
        self.clear_profiles_page_unsaved()
        return True

    def sync_profile_startup_controls(self):
        """
        Keep Enable profile function and startup radio buttons in sync with
        the saved configuration values while Configure is open.
        """
        self.updating_profile_startup_controls = True
        try:
            enabled = self.profile_function_is_enabled()
            mode = self.get_profile_startup_mode()

            # A startup choice must not point to a profile
            # that no longer exists. However, during Gramps startup the
            # family-tree identity may not be ready yet. In that early state
            # we keep the saved Standard-profile choice instead of changing
            # it to No profile by mistake.
            standard_context_ready = self.standard_profile_database_context_ready()
            if (mode == 'standard' and standard_context_ready and
                    not self.standard_graphview_profile_exists()):
                mode = 'none'
                self.set_profile_startup_mode('none')

            if self.profile_feature_enable_checkbox is not None:
                self.profile_feature_enable_checkbox.set_active(enabled)

            if self.profile_temporary_checkbox is not None:
                self.profile_temporary_checkbox.set_active(
                    self.profiles_temporary_is_enabled())

            if mode == 'standard' and self.profile_startup_standard_radio is not None:
                self.profile_startup_standard_radio.set_active(True)
            elif mode == 'view' and self.profile_startup_view_radio is not None:
                # If no View profile is currently loaded, show
                # "No profile" in the open Configure dialog and keep the
                # "Current View profile" radio locked. Do not rewrite the
                # startup JSON here. At program startup, this method can run
                # before the saved View profile has been auto-loaded, and
                # changing startup_mode to "none" would prevent startup
                # loading from working.
                if self.current_view_profile_filename:
                    self.profile_startup_view_radio.set_active(True)
                elif self.profile_startup_none_radio is not None:
                    self.profile_startup_none_radio.set_active(True)
            elif self.profile_startup_none_radio is not None:
                self.profile_startup_none_radio.set_active(True)

            for radio in (
                    self.profile_startup_none_radio,
                    self.profile_startup_standard_radio,
                    self.profile_startup_view_radio):
                if radio is not None:
                    radio.set_sensitive(enabled)

            self.update_profile_function_controls_sensitivity()
        finally:
            self.updating_profile_startup_controls = False

    def cb_profile_feature_enable_toggled(self, checkbutton):
        """
        Enable/disable the profile function from the Profiles page.
        """
        if getattr(self, 'updating_profile_startup_controls', False):
            return

        wanted_enabled = checkbutton.get_active()
        current_enabled = self.profile_function_is_enabled()

        if wanted_enabled == current_enabled:
            return

        if wanted_enabled:
            if not self.enable_profile_function():
                self.sync_profile_startup_controls()
            return

        if not self.disable_profile_function():
            self.sync_profile_startup_controls()

    def cb_profile_startup_mode_toggled(self, radiobutton, startup_mode):
        """
        Save the selected startup mode. Loading is still guarded separately
        and only runs when the profile function is enabled.
        """
        if getattr(self, 'updating_profile_startup_controls', False):
            return

        if not self.profile_function_action_allowed():
            return

        if not radiobutton.get_active():
            return

        if (startup_mode == 'standard' and
                self.standard_profile_database_context_ready() and
                not self.standard_graphview_profile_exists()):
            self.set_profile_startup_mode('none')
            self.sync_profile_startup_controls()
            return

        if startup_mode == 'view':
            # Do not allow choosing Current View profile unless
            # one is currently loaded. A remembered startup filename from an
            # earlier session is not enough for a new user selection.
            if self.current_view_profile_filename:
                self.remember_startup_view_profile(
                    self.current_view_profile_filename,
                    self.current_view_profile_name)
            else:
                self.set_profile_startup_mode('none')
                self.sync_profile_startup_controls()
                return

        if startup_mode not in ('none', 'standard', 'view'):
            startup_mode = 'none'

        self.set_profile_startup_mode(startup_mode)

    def build_standard_profile_data(self):
        """
        Build a Standard profile for this family tree.
        Standard profiles contain only layout, display and style settings.
        """
        db_name, media_path, db_internal_path = self.get_graphview_db_profile_info()

        def get_config_value(config_key):
            """Read a Graph View config value."""
            return self._config.get(config_key)

        profile = {
            "profile_version": 1,
            "profile_name": "",
            "profile_type": "standard_profile",
            "created_at": datetime.now().isoformat(timespec="seconds"),
            "db_name": db_name,
            "media_path": media_path,
            "db_internal_path": db_internal_path,
            "content": {
                # Always record the actual value, including 0
                # (unlimited), independently of the profile checkbox.
                "interface.graphview-people-limit": get_config_value(
                    "interface.graphview-people-limit"),
            },
            "layout": {
                "interface.graphview-direction": get_config_value(
                    "interface.graphview-direction"),
                "interface.graphview-show-lines": get_config_value(
                    "interface.graphview-show-lines"),
                "interface.graphview-ranksep": get_config_value(
                    "interface.graphview-ranksep"),
                "interface.graphview-nodesep": get_config_value(
                    "interface.graphview-nodesep"),
            },
            "display": {
                "interface.graphview-show-images": get_config_value(
                    "interface.graphview-show-images"),
                "interface.graphview-show-id": get_config_value(
                    "interface.graphview-show-id"),
                "interface.graphview-show-avatars": get_config_value(
                    "interface.graphview-show-avatars"),
                "interface.graphview-show-full-dates": get_config_value(
                    "interface.graphview-show-full-dates"),
                "interface.graphview-show-places": get_config_value(
                    "interface.graphview-show-places"),
                "interface.graphview-place-format": get_config_value(
                    "interface.graphview-place-format"),
                "interface.graphview-show-tags": get_config_value(
                    "interface.graphview-show-tags"),
                "interface.graphview-filter-family-tag": get_config_value(
                    "interface.graphview-filter-family-tag"),
            },
            "style": {
                "interface.graphview-highlight-home-person": get_config_value(
                    "interface.graphview-highlight-home-person"),
                "interface.graphview-home-path-color": get_config_value(
                    "interface.graphview-home-path-color"),
                "interface.graphview-person-theme": get_config_value(
                    "interface.graphview-person-theme"),
                "interface.graphview-font": get_config_value(
                    "interface.graphview-font"),
                "interface.graphview-avatars-style": get_config_value(
                    "interface.graphview-avatars-style"),
                "interface.graphview-person-border-size": get_config_value(
                    "interface.graphview-person-border-size"),
                "interface.graphview-active-person-border-size": get_config_value(
                    "interface.graphview-active-person-border-size"),
                "interface.graphview-avatars-male": get_config_value(
                    "interface.graphview-avatars-male"),
                "interface.graphview-avatars-female": get_config_value(
                    "interface.graphview-avatars-female"),
                "interface.graphview-avatars-unknown": get_config_value(
                    "interface.graphview-avatars-unknown"),
                "interface.graphview-avatars-other": get_config_value(
                    "interface.graphview-avatars-other"),
            },
        }

        return self.apply_avatar_profile_save_rules(profile)

    def build_full_current_standard_profile_data(self):
        """Build a Standard profile containing every supported setting.

        This is used by the beginner-friendly
        "Save as Standard profile" button. It reads the current Graph View
        directly and does not depend on the individual profile checkboxes.
        Saving the snapshot must not change or reload the graph.
        """
        profile = self.build_standard_profile_data()

        content = profile.get('content')
        if not isinstance(content, dict):
            content = {}
            profile['content'] = content

        content['interface.graphview-ancestor-generations'] = self._config.get(
            'interface.graphview-ancestor-generations')
        content['interface.graphview-descendant-generations'] = self._config.get(
            'interface.graphview-descendant-generations')
        content['interface.graphview-show-all-connected'] = self._config.get(
            'interface.graphview-show-all-connected')

        limit_value = self._config.get('interface.graphview-people-limit')
        self.set_profile_people_limit_choice(
            profile, self.graphview_people_limit_is_real_limit(limit_value),
            limit_value)

        if self.graph_widget is not None:
            try:
                profile['view_state_optional'] = {
                    'interface.graphview-scale': self.graph_widget.scale,
                    'horizontal_adjustment_value': (
                        self.graph_widget.hadjustment.get_value()),
                    'vertical_adjustment_value': (
                        self.graph_widget.vadjustment.get_value()),
                }
            except Exception:
                profile.pop('view_state_optional', None)

        return self.apply_avatar_profile_save_rules(profile)

    def get_standard_profile_group_key_map(self):
        """
        Map Standard-profile group checkboxes to the
        config keys they include/exclude in the standard JSON file.

        When a group is not selected, its keys are removed from the JSON.
        The load code will then ignore those settings.
        """
        return {
            'time_direction': (
                'layout',
                ('interface.graphview-direction',)),
            'theme': (
                'style',
                ('interface.graphview-person-theme',)),
            'path_color': (
                'style',
                ('interface.graphview-home-path-color',)),
            'font': (
                'style',
                ('interface.graphview-font',)),
            'active_person_border_size': (
                'style',
                ('interface.graphview-active-person-border-size',)),
            'person_border_size': (
                'style',
                ('interface.graphview-person-border-size',)),
            'line_types': (
                'layout',
                ('interface.graphview-show-lines',)),
            'generations': (
                'content',
                ('interface.graphview-ancestor-generations',
                 'interface.graphview-descendant-generations')),
            'people_limit': (
                'content',
                ('interface.graphview-people-limit',)),
            'spacings': (
                'layout',
                ('interface.graphview-ranksep',
                 'interface.graphview-nodesep')),
            'view_state': (
                'view_state_optional',
                ('interface.graphview-scale',
                 'horizontal_adjustment_value',
                 'vertical_adjustment_value')),
        }

    def standard_profile_group_is_enabled(self, group_name, default_value=True):
        """
        Return whether a Standard-profile group is present in the saved
        Standard profile.
        """
        group_map = self.get_standard_profile_group_key_map()
        group_info = group_map.get(group_name)
        if not group_info:
            return default_value

        section_name, config_keys = group_info
        section = self.get_standard_profile_section_for_choices(section_name)
        if not section:
            # No Standard profile means a clean Standard column.
            return False

        if group_name == 'people_limit':
            profile = self.read_standard_profile_for_choices()
            return self.get_profile_people_limit_choice(profile, False)

        return all(config_key in section for config_key in config_keys)

    def read_standard_profile_for_choices(self):
        """
        Read the saved Standard profile used by the Profiles-tab checkboxes.

        Standard checkbox states must represent the saved
        Standard JSON file, not the current live Graph View configuration.
        Therefore Configure reopen must not make the Standard column follow
        changes made on the other Configure pages.
        """
        try:
            self.clean_first_standard_profile_if_created_from_backup()
            filename = self.get_standard_profile_filename()
            if not os.path.isfile(filename):
                return {}
            with open(filename, 'r', encoding='utf-8') as json_file:
                profile = json.load(json_file)
            if isinstance(profile, dict):
                return profile
        except Exception:
            pass
        return {}

    def get_standard_profile_choice_value(self, profile, config_key,
                                          default_value=False):
        """
        Return a saved config value from the Standard-profile JSON.

        Direct Standard-profile boolean rows such as Show IDs, Show images,
        Highlight home person, Show people with the person tag "ProfileTag" and All connected
        are values in the saved profile. They must not be read from
        self._config when building or refreshing the Profiles page, because
        self._config is the current live graph state.
        """
        if not isinstance(profile, dict):
            return default_value

        if config_key == 'interface.graphview-show-avatars':
            display = profile.get('display', {})
            if isinstance(display, dict):
                return bool(
                    display.get('interface.graphview-show-images', False) and
                    display.get('interface.graphview-show-avatars', False))
            return False

        for section_name in ('display', 'style', 'content', 'layout'):
            section = profile.get(section_name, {})
            if isinstance(section, dict) and config_key in section:
                value = section[config_key]
                if (config_key == 'interface.graphview-filter-family-tag' and
                        value and
                        not self.graphview_family_tag_exists()):
                    return False
                return value

        return default_value

    def apply_standard_profile_save_choices(self, profile):
        """
        Keep the existing JSON values.

        The simple live Standard-profile boxes are saved as normal true/false
        values. The remaining Standard-profile boxes are group/include choices:
        when a group is selected, its current Gramps values are written to the
        JSON; when a group is not selected, its keys are removed so they are
        not restored on load.
        """
        def get_config_value(config_key):
            """Read a Graph View config value."""
            return self._config.get(config_key)

        def get_view_state_value(config_key):
            """Read current zoom and chart position from Graph Widget."""
            if not self.graph_widget:
                return None

            if config_key == 'interface.graphview-scale':
                return self.graph_widget.scale

            if config_key == 'horizontal_adjustment_value':
                return self.graph_widget.hadjustment.get_value()

            if config_key == 'vertical_adjustment_value':
                return self.graph_widget.vadjustment.get_value()

            return None

        sections = {
            'layout': profile.get('layout', {}),
            'display': profile.get('display', {}),
            'style': profile.get('style', {}),
            'content': profile.get('content', {}),
            'view_state_optional': profile.get('view_state_optional', {}),
        }
        if not isinstance(sections['content'], dict):
            sections['content'] = {}
        profile['content'] = sections['content']
        if not isinstance(sections['view_state_optional'], dict):
            sections['view_state_optional'] = {}
        profile['view_state_optional'] = sections['view_state_optional']

        # Simple live boolean values: the checkbox is the value itself.
        # When the Standard profile has been deleted, the
        # Standard column can be cleared visually without changing the graph.
        # If the user saves from that clean state, the saved profile should
        # follow the checkboxes, not the untouched live Graph View config.
        display = sections.get('display')
        if isinstance(display, dict):
            save_choices = getattr(self, 'standard_profile_save_choices', {})
            for config_key in (
                'interface.graphview-show-images',
                'interface.graphview-show-id',
                'interface.graphview-show-avatars',
                'interface.graphview-show-full-dates',
                'interface.graphview-show-places',
                'interface.graphview-show-tags',
            ):
                display[config_key] = save_choices.get(
                    config_key, get_config_value(config_key))

            # Place format belongs together with Show places,
            # like avatar style belongs together with Show avatars.
            display['interface.graphview-place-format'] = (
                get_config_value('interface.graphview-place-format'))

            # This checkbox is a real true/false setting, not a group choice.
            # It does not redraw live from the Profiles page,
            # but Save standard profile must store the checkbox value.
            save_choices = getattr(self, 'standard_profile_save_choices', {})
            filter_value = save_choices.get(
                'interface.graphview-filter-family-tag',
                get_config_value('interface.graphview-filter-family-tag'))
            if (filter_value and
                    not self.family_tag_filter_value_is_allowed(True)):
                filter_value = False
            display['interface.graphview-filter-family-tag'] = filter_value

        style = sections.get('style')
        if isinstance(style, dict):
            save_choices = getattr(self, 'standard_profile_save_choices', {})
            style['interface.graphview-highlight-home-person'] = (
                save_choices.get(
                    'interface.graphview-highlight-home-person',
                    get_config_value(
                        'interface.graphview-highlight-home-person')))

            # Collect avatar style values here. The dependency rule below removes them
            # unless both Show images and Show avatars & style are true.
            for config_key in (
                'interface.graphview-avatars-style',
                'interface.graphview-avatars-male',
                'interface.graphview-avatars-female',
                'interface.graphview-avatars-unknown',
                'interface.graphview-avatars-other',
            ):
                style[config_key] = get_config_value(config_key)

        # Standard-profile save-only boolean values: the checkbox is the
        # value that should be written to the standard profile. These do not
        # need live redraw from the Profiles page.
        content = sections.get('content')
        if isinstance(content, dict):
            save_choices = getattr(self, 'standard_profile_save_choices', {})
            content['interface.graphview-show-all-connected'] = (
                save_choices.get(
                    'interface.graphview-show-all-connected',
                    get_config_value('interface.graphview-show-all-connected')))

        # Group/include choices: selected means save and restore later.
        group_choices = getattr(self, 'standard_profile_group_choices', {})
        for group_name, (section_name, config_keys) in (
                self.get_standard_profile_group_key_map().items()):
            section = sections.get(section_name)
            if not isinstance(section, dict):
                continue

            group_enabled = group_choices.get(group_name, True)

            # Limit number displayed is different from
            # the other include/exclude groups. Its numeric value is always
            # written, including 0 = unlimited. The checkbox choice for a
            # positive value is stored separately.
            if group_name == 'people_limit':
                limit_value = get_config_value(
                    'interface.graphview-people-limit')
                self.set_profile_people_limit_choice(
                    profile, group_enabled, limit_value)
                continue

            if group_enabled:
                for config_key in config_keys:
                    if section_name == 'view_state_optional':
                        section[config_key] = get_view_state_value(config_key)
                    else:
                        section[config_key] = get_config_value(config_key)
            else:
                for config_key in config_keys:
                    section.pop(config_key, None)

        if isinstance(profile.get('content'), dict) and not profile['content']:
            profile.pop('content', None)

        if (isinstance(profile.get('view_state_optional'), dict) and
                not profile['view_state_optional']):
            profile.pop('view_state_optional', None)

        return self.apply_avatar_profile_save_rules(profile)

    def save_standard_graphview_profile(self, show_message=True,
                                        save_all_supported=False):
        """
        Save the Standard profile for this family tree.

        When save_all_supported is True, capture every supported current
        Graph View setting instead of using the individual profile choices.
        """
        if not self.profile_function_is_enabled():
            return False

        filename = self.get_standard_profile_filename()
        if save_all_supported:
            profile = self.build_full_current_standard_profile_data()
        else:
            profile = self.build_standard_profile_data()
            profile = self.apply_standard_profile_save_choices(profile)
        profile["profile_name"] = os.path.splitext(os.path.basename(filename))[0]

        try:
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            with open(filename, 'w', encoding='utf-8') as json_file:
                json.dump(profile, json_file, ensure_ascii=False, indent=2)
        except OSError as msg:
            if show_message:
                ErrorDialog(
                    _('Could not save Graph View standard profile'),
                    str(msg),
                    parent=self.uistate.window)
            return False

        self.standard_profile_controls_active = True

        if show_message:
            dialog = Gtk.MessageDialog(
                transient_for=self.uistate.window,
                modal=True,
                message_type=Gtk.MessageType.INFO,
                buttons=Gtk.ButtonsType.OK,
                text=_('Standard profile saved'))
            dialog.format_secondary_text(filename)
            dialog.run()
            dialog.destroy()

        return True

    def load_standard_graphview_profile(self, _button=None):
        """
        Load this family tree's saved Standard profile manually.

        A missing Standard profile is never created
        automatically. The ordinary UI keeps
        this action disabled while the file is missing; the explicit file
        check below is a final safety net. Loading a Standard profile also
        clears the current View profile status, because the active graph is no
        longer the loaded View profile.
        """
        if not self.profile_function_action_allowed():
            return

        self.clean_first_standard_profile_if_created_from_backup()
        filename = self.get_standard_profile_filename()

        # A saved Standard profile is required. This can still
        # be reached if the file is removed manually
        # while Configure is open, so keep a clear message as a safety net.
        if not filename or not os.path.isfile(filename):
            WarningDialog(
                _('No standard profile'),
                _('There is no saved Standard Graph View profile to load for this family tree.'),
                parent=self.uistate.window)
            self.update_profiles_status_labels()
            return

        try:
            with open(filename, 'r', encoding='utf-8') as json_file:
                profile = json.load(json_file)
        except (OSError, json.JSONDecodeError) as msg:
            ErrorDialog(
                _('Could not load Graph View standard profile'),
                str(msg),
                parent=self.uistate.window)
            return

        # Explain changed family-tree information before
        # applying anything, while still allowing a restored/moved copy.
        if not self.confirm_graphview_profile_database_context(
                profile, 'standard_profile'):
            return

        if not self.apply_standard_graphview_profile(profile):
            WarningDialog(
                _('Could not load Graph View standard profile'),
                _('The selected standard profile could not be applied.'),
                parent=self.uistate.window)
            return

        self.set_current_view_profile('', '')
        self.reset_view_profile_save_choices()
        self.clear_profiles_page_unsaved()
        self.update_profiles_status_labels()

    def get_empty_view_profile_save_choices(self):
        """
        Return a clean/empty View-profile choice state.

        When no View profile is active, the View column must
        not show old default choices. Boolean rows are stored here too so the
        visible checkbox state and the saved JSON stay in sync.
        """
        return {
            'home_person': False,
            'active_person': False,
            'time_direction': False,
            'people_limit': False,
            'theme': False,
            'path_color': False,
            'font': False,
            'active_person_border_size': False,
            'person_border_size': False,
            'line_types': False,
            'generations': False,
            'spacings': False,
            'view_state': False,
            'interface.graphview-show-id': False,
            'interface.graphview-show-images': False,
            'interface.graphview-show-avatars': False,
            'interface.graphview-highlight-home-person': False,
            'interface.graphview-show-full-dates': False,
            'interface.graphview-show-places': False,
            'interface.graphview-show-tags': False,
            'interface.graphview-filter-family-tag': False,
            'interface.graphview-show-all-connected': False,
        }

    def get_full_current_view_profile_choices(self):
        """Return choices for a complete snapshot of the current view.

        Boolean rows store their actual current true/false value,
        while every supported include/exclude group is selected. A people
        limit of 0 stays unselected because 0 is always saved and means
        unlimited.
        """
        show_images = bool(
            self._config.get('interface.graphview-show-images'))
        show_avatars = bool(
            show_images and
            self._config.get('interface.graphview-show-avatars'))
        limit_value = self._config.get('interface.graphview-people-limit')

        return {
            'home_person': True,
            'active_person': True,
            'time_direction': True,
            'people_limit': self.graphview_people_limit_is_real_limit(
                limit_value),
            'theme': True,
            'path_color': True,
            'font': True,
            'active_person_border_size': True,
            'person_border_size': True,
            'line_types': True,
            'generations': True,
            'spacings': True,
            'view_state': True,
            'interface.graphview-show-id': bool(
                self._config.get('interface.graphview-show-id')),
            'interface.graphview-show-images': show_images,
            'interface.graphview-show-avatars': show_avatars,
            'interface.graphview-highlight-home-person': bool(
                self._config.get(
                    'interface.graphview-highlight-home-person')),
            'interface.graphview-show-full-dates': bool(
                self._config.get('interface.graphview-show-full-dates')),
            'interface.graphview-show-places': bool(
                self._config.get('interface.graphview-show-places')),
            'interface.graphview-show-tags': bool(
                self._config.get('interface.graphview-show-tags')),
            'interface.graphview-filter-family-tag': bool(
                self._config.get(
                    'interface.graphview-filter-family-tag')),
            'interface.graphview-show-all-connected': bool(
                self._config.get(
                    'interface.graphview-show-all-connected')),
        }

    def set_current_view_profile(self, filename, profile_name=None):
        """
        Remember which View profile is currently active in this Graph View.
        """
        self.current_view_profile_filename = filename or ''
        if profile_name is None and filename:
            profile_name = os.path.splitext(os.path.basename(filename))[0]
        self.current_view_profile_name = profile_name or ''

        # If Current View profile is selected for startup,
        # keep the JSON filename in our startup-settings file. The mode
        # alone is not enough after Gramps has been closed and opened again.
        if filename and self.get_profile_startup_mode() == 'view':
            self.remember_startup_view_profile(filename, profile_name)

        self.update_profiles_status_labels()
        self.update_profile_function_controls_sensitivity()

    def reset_view_profile_save_choices(self):
        """
        Reset View-profile save choices to a clean/no-profile state.
        """
        self.view_profile_save_choices = self.get_empty_view_profile_save_choices()
        self.sync_view_profile_controls()

    def cb_profile_view_choice_toggled(self, checkbutton, choice_key):
        """
        Remember what the View profile should save and restore.

        These checkboxes are include/exclude choices. They do not change the
        current graph when toggled; they only decide whether the related data
        is written to the View profile JSON.
        """
        if getattr(self, 'updating_view_profile_controls', False):
            return

        if not self.profile_function_action_allowed():
            return

        if not hasattr(self, 'view_profile_save_choices'):
            self.view_profile_save_choices = {}
        self.view_profile_save_choices[choice_key] = checkbutton.get_active()
        self.mark_profiles_page_unsaved()

    def cb_profile_view_bool_toggled(self, checkbutton, config_key):
        """
        Let selected boolean View-profile boxes update Graph View immediately.

        These checkboxes are real true/false values, like the same boxes in
        the Standard profile column. They stay in the JSON as true or false
        when the View profile is saved.
        """
        if getattr(self, 'updating_view_profile_controls', False):
            return

        if not self.profile_function_action_allowed():
            return

        value = checkbutton.get_active()
        if (config_key == 'interface.graphview-filter-family-tag' and
                value and
                not self.family_tag_filter_value_is_allowed(True)):
            self.updating_view_profile_controls = True
            try:
                checkbutton.set_active(False)
            finally:
                self.updating_view_profile_controls = False
            value = False

        if not hasattr(self, 'view_profile_save_choices'):
            self.view_profile_save_choices = self.get_empty_view_profile_save_choices()
        self.view_profile_save_choices[config_key] = value
        self._config.set(config_key, value)

        if config_key == 'interface.graphview-show-id':
            self.show_ID = value
        elif config_key == 'interface.graphview-show-images':
            self.show_images = value
        elif config_key == 'interface.graphview-show-avatars':
            self.show_avatars = value
        elif config_key == 'interface.graphview-highlight-home-person':
            self.highlight_home_person = value
        elif config_key == 'interface.graphview-show-full-dates':
            self.show_full_dates = value
        elif config_key == 'interface.graphview-show-places':
            self.show_places = value
        elif config_key == 'interface.graphview-show-tags':
            self.show_tag_color = value
        elif config_key == 'interface.graphview-show-all-connected':
            if self.graph_widget and hasattr(self.graph_widget, 'all_connected_btn'):
                if self.graph_widget.all_connected_btn.get_active() != value:
                    self.graph_widget.all_connected_btn.set_active(value)

        self.update_profile_avatar_controls_sensitivity()
        self.mark_profiles_page_unsaved()

        if self.graph_widget and self.get_active():
            self.graph_widget.populate(self.get_active())

    def sync_view_profile_controls(self, profile=None):
        """
        Update View-profile checkboxes from the current loaded profile.

        Include/exclude choices are shown as selected only when their data is
        present in a loaded JSON file. Boolean choices show the true/false
        value that is currently active in Graph View.
        """
        if not hasattr(self, 'view_profile_save_choices'):
            self.view_profile_save_choices = self.get_empty_view_profile_save_choices()

        # When there is no active View profile and no profile
        # was passed in, keep the View column completely clean. Do not copy
        # current GraphView config values into the View profile column.
        if not isinstance(profile, dict) and not self.current_view_profile_filename:
            self.view_profile_save_choices = self.get_empty_view_profile_save_choices()

        if isinstance(profile, dict):
            active_data = profile.get('active_person')
            home_data = profile.get('home_person')
            display_data = profile.get('display')

            self.view_profile_save_choices['active_person'] = (
                isinstance(active_data, dict) and bool(active_data))
            self.view_profile_save_choices['home_person'] = (
                isinstance(home_data, dict) and bool(home_data))

            # Boolean View-profile rows are real true/false values when they
            # exist in JSON, but no active View profile should not inherit
            # current GraphView config values.
            if isinstance(display_data, dict):
                for config_key in (
                        'interface.graphview-show-id',
                        'interface.graphview-show-images',
                        'interface.graphview-show-full-dates',
                        'interface.graphview-show-places',
                        'interface.graphview-show-tags'):
                    self.view_profile_save_choices[config_key] = bool(
                        display_data.get(config_key, False))
                self.view_profile_save_choices[
                    'interface.graphview-show-avatars'] = bool(
                        display_data.get(
                            'interface.graphview-show-images', False) and
                        display_data.get(
                            'interface.graphview-show-avatars', False))
            else:
                for config_key in (
                        'interface.graphview-show-id',
                        'interface.graphview-show-images',
                        'interface.graphview-show-avatars',
                        'interface.graphview-show-full-dates',
                        'interface.graphview-show-places',
                        'interface.graphview-show-tags'):
                    self.view_profile_save_choices[config_key] = False

            layout_data = profile.get('layout')
            self.view_profile_save_choices['time_direction'] = (
                isinstance(layout_data, dict) and
                'interface.graphview-direction' in layout_data)
            self.view_profile_save_choices['line_types'] = (
                isinstance(layout_data, dict) and
                'interface.graphview-show-lines' in layout_data)
            self.view_profile_save_choices['spacings'] = (
                isinstance(layout_data, dict) and
                'interface.graphview-ranksep' in layout_data and
                'interface.graphview-nodesep' in layout_data)

            content_data = profile.get('content')
            self.view_profile_save_choices['people_limit'] = (
                self.get_profile_people_limit_choice(profile, False))
            self.view_profile_save_choices['generations'] = (
                isinstance(content_data, dict) and
                'interface.graphview-ancestor-generations' in content_data and
                'interface.graphview-descendant-generations' in content_data)
            if isinstance(content_data, dict):
                self.view_profile_save_choices[
                    'interface.graphview-show-all-connected'] = bool(
                        content_data.get(
                            'interface.graphview-show-all-connected', False))
                filter_value = bool(
                    content_data.get(
                        'interface.graphview-filter-family-tag', False))
                if filter_value and not self.graphview_family_tag_exists():
                    filter_value = False
                self.view_profile_save_choices[
                    'interface.graphview-filter-family-tag'] = filter_value
            else:
                self.view_profile_save_choices[
                    'interface.graphview-show-all-connected'] = False
                self.view_profile_save_choices[
                    'interface.graphview-filter-family-tag'] = False

            if (isinstance(content_data, dict) and
                    'interface.graphview-show-all-connected' in content_data):
                all_connected_value = bool(
                    content_data['interface.graphview-show-all-connected'])
                self._config.set(
                    'interface.graphview-show-all-connected',
                    all_connected_value)
                if (self.graph_widget and
                        hasattr(self.graph_widget, 'all_connected_btn') and
                        self.graph_widget.all_connected_btn.get_active() !=
                        all_connected_value):
                    self.graph_widget.all_connected_btn.set_active(
                        all_connected_value)

            style_data = profile.get('style')
            self.view_profile_save_choices['theme'] = (
                isinstance(style_data, dict) and
                'interface.graphview-person-theme' in style_data)
            self.view_profile_save_choices['path_color'] = (
                isinstance(style_data, dict) and
                'interface.graphview-home-path-color' in style_data)
            self.view_profile_save_choices['font'] = (
                isinstance(style_data, dict) and
                'interface.graphview-font' in style_data)
            self.view_profile_save_choices['active_person_border_size'] = (
                isinstance(style_data, dict) and
                'interface.graphview-active-person-border-size' in style_data)
            self.view_profile_save_choices['person_border_size'] = (
                isinstance(style_data, dict) and
                'interface.graphview-person-border-size' in style_data)

            view_state_data = profile.get('view_state_optional')
            self.view_profile_save_choices['view_state'] = (
                isinstance(view_state_data, dict) and
                'interface.graphview-scale' in view_state_data and
                'horizontal_adjustment_value' in view_state_data and
                'vertical_adjustment_value' in view_state_data)

            if isinstance(display_data, dict):
                if 'interface.graphview-show-id' in display_data:
                    self._config.set(
                        'interface.graphview-show-id',
                        bool(display_data['interface.graphview-show-id']))
                    self.show_ID = bool(
                        display_data['interface.graphview-show-id'])

                if 'interface.graphview-show-images' in display_data:
                    self._config.set(
                        'interface.graphview-show-images',
                        bool(display_data['interface.graphview-show-images']))
                    self.show_images = bool(
                        display_data['interface.graphview-show-images'])

                if 'interface.graphview-show-avatars' in display_data:
                    avatar_value = bool(
                        display_data.get(
                            'interface.graphview-show-images', False) and
                        display_data['interface.graphview-show-avatars'])
                    self._config.set(
                        'interface.graphview-show-avatars', avatar_value)
                    self.show_avatars = avatar_value

                if 'interface.graphview-show-full-dates' in display_data:
                    self._config.set(
                        'interface.graphview-show-full-dates',
                        bool(display_data['interface.graphview-show-full-dates']))
                    self.show_full_dates = bool(
                        display_data['interface.graphview-show-full-dates'])

                if 'interface.graphview-show-places' in display_data:
                    self._config.set(
                        'interface.graphview-show-places',
                        bool(display_data['interface.graphview-show-places']))
                    self.show_places = bool(
                        display_data['interface.graphview-show-places'])

                if 'interface.graphview-show-tags' in display_data:
                    self._config.set(
                        'interface.graphview-show-tags',
                        bool(display_data['interface.graphview-show-tags']))
                    self.show_tag_color = bool(
                        display_data['interface.graphview-show-tags'])

            style_data = profile.get('style')
            if isinstance(style_data, dict):
                self.view_profile_save_choices[
                    'interface.graphview-highlight-home-person'] = bool(
                        style_data.get(
                            'interface.graphview-highlight-home-person', False))
                if 'interface.graphview-highlight-home-person' in style_data:
                    self._config.set(
                        'interface.graphview-highlight-home-person',
                        bool(style_data['interface.graphview-highlight-home-person']))
                    self.highlight_home_person = bool(
                        style_data['interface.graphview-highlight-home-person'])

        self.updating_view_profile_controls = True
        try:
            for info in getattr(self, 'profile_view_checkbox_info', []):
                checkbutton = info.get('checkbutton')
                if checkbutton is None:
                    continue

                choice_key = info.get('choice_key')
                view_config_key = info.get('view_config_key')
                default_value = info.get('default_value', True)

                if view_config_key:
                    checkbutton.set_active(bool(
                        self.view_profile_save_choices.get(
                            view_config_key, False)))
                elif choice_key:
                    checkbutton.set_active(bool(
                        self.view_profile_save_choices.get(
                            choice_key, default_value)))
                else:
                    checkbutton.set_active(bool(default_value))
        finally:
            self.updating_view_profile_controls = False

        self.update_profile_avatar_controls_sensitivity()
        self.update_profile_people_limit_controls_sensitivity()
        return False

    def clear_view_profile_controls(self):
        """
        Clear the View-profile column after a View profile is deleted.

        This is only a profile-page reset. It must not change current
        Graph View settings or redraw the graph.
        """
        self.view_profile_save_choices = self.get_empty_view_profile_save_choices()

        self.updating_view_profile_controls = True
        try:
            for info in getattr(self, 'profile_view_checkbox_info', []):
                checkbutton = info.get('checkbutton')
                if checkbutton is not None:
                    checkbutton.set_active(False)
        finally:
            self.updating_view_profile_controls = False

        self.update_profile_function_controls_sensitivity()
        return False

    def mark_profiles_page_unsaved(self):
        """
        Remember that the Profiles page has choices not saved to a
        Standard/View profile yet.
        """
        self.profiles_page_has_unsaved_changes = True

    def clear_profiles_page_unsaved(self):
        """
        Clear the Profiles-page unsaved-changes warning flag.
        """
        self.profiles_page_has_unsaved_changes = False

    def request_profiles_configure_close(self):
        """
        Close the Gramps Configure dialog through its normal response path.

        The close-button guard opens a modal warning during
        button-press/key/click handling. After the user chooses "Close
        anyway", the original button activation can no longer be trusted to
        finish normally. Schedule a normal GTK CLOSE response and stop the
        original button event, so one user click closes both the warning and
        Configure.
        """
        window = getattr(self, 'profiles_config_window', None)
        if window is None:
            return False

        if getattr(self, 'profiles_config_force_close_once', False):
            return True

        self.profiles_config_force_close_once = True

        def do_close():
            try:
                window.response(Gtk.ResponseType.CLOSE)
            except Exception:
                # Last-resort fallback only. The normal path above is preferred
                # because Gramps' ConfigureDialog closes through response.
                try:
                    window.destroy()
                except Exception:
                    pass
            return False

        try:
            GLib.idle_add(do_close)
        except Exception:
            do_close()

        return True

    def confirm_close_profiles_with_unsaved_changes(self):
        """
        Ask before closing Configure when Profiles choices were changed but
        not saved to a profile. Return True when closing is allowed.
        """
        if not getattr(self, 'profiles_page_has_unsaved_changes', False):
            return True

        parent = getattr(self, 'profiles_config_window', None)
        if parent is None:
            parent = self.uistate.window

        dialog = Gtk.MessageDialog(
            transient_for=parent,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Profiles have unsaved changes'))
        dialog.format_secondary_text(
            _('Some profile choices may not have been saved to a profile.\n'
              'Go back and save them?'))
        dialog.add_button(_('Go back'), Gtk.ResponseType.YES)
        dialog.add_button(_('Close anyway'), Gtk.ResponseType.NO)

        response = dialog.run()
        dialog.destroy()

        if response == Gtk.ResponseType.YES:
            return False

        self.clear_profiles_page_unsaved()
        return True

    def cb_profiles_configure_delete_event(self, _window, _event):
        """
        Stop Configure from closing if Profiles choices may be unsaved.
        """
        return not self.confirm_close_profiles_with_unsaved_changes()

    def cb_profiles_configure_response(self, window, _response_id):
        """
        Extra guard for Configure dialogs that close through a response
        signal instead of the window delete-event.
        """
        if getattr(self, 'profiles_config_force_close_once', False):
            self.profiles_config_force_close_once = False
            return False

        if self.confirm_close_profiles_with_unsaved_changes():
            return False

        try:
            window.stop_emission_by_name('response')
        except Exception:
            pass
        return True

    def cb_profiles_configure_close_button_press(self, button, _event):
        """
        Guard the Configure Close button before its normal click handler runs.

        Some Gramps Configure windows close from the button activation path
        instead of the window delete-event. Catching button-press-event gives
        us one chance before the normal clicked/response handling starts.
        """
        if self.confirm_close_profiles_with_unsaved_changes():
            self.request_profiles_configure_close()

        try:
            button.stop_emission_by_name('button-press-event')
        except Exception:
            pass
        return True

    def cb_profiles_configure_close_button_key_press(self, button, event):
        """
        Guard keyboard activation of the Configure Close button.
        """
        try:
            keyval = event.keyval
        except Exception:
            keyval = None

        if keyval not in (Gdk.KEY_Return, Gdk.KEY_KP_Enter, Gdk.KEY_space):
            return False

        if self.confirm_close_profiles_with_unsaved_changes():
            self.request_profiles_configure_close()

        try:
            button.stop_emission_by_name('key-press-event')
        except Exception:
            pass
        return True

    def cb_profiles_configure_close_button_clicked(self, button):
        """
        Fallback guard if the button was activated without a button/key press.
        """
        if self.confirm_close_profiles_with_unsaved_changes():
            self.request_profiles_configure_close()

        try:
            button.stop_emission_by_name('clicked')
        except Exception:
            pass
        return True

    def install_profiles_close_button_guard(self, window):
        """
        Find the actual Configure Close button and guard it directly.

        The button is part of Gramps' general Configure dialog, not GraphView
        itself, so it is found after the Profiles page has been built.
        """
        if window is None:
            return False

        close_labels = ('close', 'luk')

        def normalized_button_label(button):
            label = ''
            try:
                label = button.get_label() or ''
            except Exception:
                label = ''
            return label.replace('_', '').strip().lower()

        def walk(widget):
            try:
                if isinstance(widget, Gtk.Button):
                    label = normalized_button_label(widget)
                    if label in close_labels and id(widget) not in (
                            self.profiles_config_close_button_ids):
                        self.profiles_config_close_button_ids.add(id(widget))
                        widget.connect(
                            'button-press-event',
                            self.cb_profiles_configure_close_button_press)
                        widget.connect(
                            'key-press-event',
                            self.cb_profiles_configure_close_button_key_press)
                        widget.connect(
                            'clicked',
                            self.cb_profiles_configure_close_button_clicked)
            except Exception:
                pass

            try:
                if isinstance(widget, Gtk.Container):
                    for child in widget.get_children():
                        walk(child)
            except Exception:
                pass

        try:
            walk(window)
        except Exception:
            pass

        return False

    def update_profiles_status_labels(self):
        """
        Refresh status labels on the Profiles page if the page is open.
        """
        if self.current_view_profile_status_label is not None:
            current_text = _('Current View profile: none')
            if self.current_view_profile_name:
                current_text = (_('Current View profile: %s') %
                                self.current_view_profile_name)
            self.current_view_profile_status_label.set_text(current_text)

        standard_context_ready = self.standard_profile_database_context_ready()
        standard_profile_exists = (
            standard_context_ready and self.standard_graphview_profile_exists())

        if self.standard_profile_status_label is not None:
            standard_text = _('Standard profile: not saved')
            if standard_profile_exists:
                standard_text = _('Standard profile: saved')
            self.standard_profile_status_label.set_text(standard_text)

        if self.standard_profile_load_button is not None:
            # Default is not an alternative profile type.
            # Keep one stable label and disable the button when no saved
            # Standard profile exists.
            self.standard_profile_load_button.set_label(
                _('Load standard profile'))

        has_current_view_profile = bool(self.current_view_profile_filename)

        # Startup choice UI only. The current View-profile
        # startup option can only be selected when a View profile is active.
        self.sync_profile_startup_controls()
        self.update_profile_function_controls_sensitivity()

    def confirm_overwrite_standard_profile(self):
        """Ask before replacing the saved Standard profile."""
        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Overwrite Standard profile?'))
        dialog.format_secondary_text(
            _('The saved Standard profile will be replaced by the current '
              'Graph View settings.'))
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('_Save'), Gtk.ResponseType.OK)
        response = dialog.run()
        dialog.destroy()
        return response == Gtk.ResponseType.OK

    def standard_profile_active_matches_home_for_save(self):
        """
        Return True when a Standard profile can represent the visible graph.

        A Standard profile never stores Home person or Active person. Both
        Standard-profile save buttons therefore use this same guard.
        """
        active_handle = self.get_active() or ''
        home_person = self.dbstate.db.get_default_person()
        home_handle = home_person.get_handle() if home_person else ''

        if active_handle == home_handle:
            return True

        WarningDialog(
            _('Cannot save Standard profile'),
            _('The active person is different from the home person.\n'
              'A Standard profile does not save the home or active person. '
              'Please use a View profile.'),
            parent=self.uistate.window)
        return False

    def standard_profile_has_selected_choices(self):
        """Return True when at least one Standard-profile box is selected."""
        checkbuttons = getattr(self, 'profile_standard_checkbuttons', [])
        if checkbuttons:
            for checkbutton in checkbuttons:
                try:
                    if checkbutton.get_active():
                        return True
                except Exception:
                    pass
            return False

        # Fallback for callers without an open Profiles page.
        save_choices = getattr(self, 'standard_profile_save_choices', {})
        group_choices = getattr(self, 'standard_profile_group_choices', {})
        return bool(
            any(bool(value) for value in save_choices.values()) or
            any(bool(value) for value in group_choices.values()))

    def confirm_save_empty_standard_profile(self):
        """Ask before saving a Standard profile with no selected boxes."""
        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('No checkboxes are selected for this Standard profile.'))
        dialog.format_secondary_text(_('Save anyway?'))
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('Save anyway'), Gtk.ResponseType.OK)
        response = dialog.run()
        dialog.destroy()
        return response == Gtk.ResponseType.OK

    def save_selected_standard_profile(self, _button=None):
        """Save the Standard column after the shared safety checks."""
        if not self.profile_function_action_allowed():
            return

        # The lower Save standard profile button follows the
        # same Active/Home rule as Save as Standard profile above.
        if not self.standard_profile_active_matches_home_for_save():
            return

        # Match the existing neutral warning for an empty View profile.
        if not self.standard_profile_has_selected_choices():
            if not self.confirm_save_empty_standard_profile():
                return

        self.save_graphview_profile(_button, 'standard_profile')

    def save_current_view_as_standard_profile(self, _button=None):
        """Save every supported current setting as Standard profile."""
        if not self.profile_function_action_allowed():
            return

        # Both Standard-profile save paths use the same
        # guard before any overwrite confirmation or file write.
        if not self.standard_profile_active_matches_home_for_save():
            return

        filename = self.get_standard_profile_filename()
        if os.path.isfile(filename):
            if not self.confirm_overwrite_standard_profile():
                return

        if self.save_standard_graphview_profile(
                show_message=True, save_all_supported=True):
            # Show exactly what the new file contains, without loading it or
            # changing the graph.
            self.sync_standard_profile_controls()
            self.clear_profiles_page_unsaved()
            self.update_profiles_status_labels()

    def save_current_view_as_new_view_profile(self, _button=None):
        """Save every supported current setting as a new View profile."""
        if not self.profile_function_action_allowed():
            return
        self.save_graphview_profile(
            None, 'view_profile', save_all_supported=True)

    def confirm_overwrite_current_view_profile(self):
        """
        Ask before overwriting the currently active View profile.
        """
        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Overwrite current View profile?'))
        profile_name = self.current_view_profile_name
        if not profile_name and self.current_view_profile_filename:
            profile_name = os.path.splitext(
                os.path.basename(self.current_view_profile_filename))[0]
        dialog.format_secondary_text(profile_name or _('Current View profile'))
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('_Save'), Gtk.ResponseType.OK)
        response = dialog.run()
        dialog.destroy()
        return response == Gtk.ResponseType.OK

    def view_profile_has_selected_choices(self):
        """
        Return True when at least one View-profile checkbox is selected.

        A visually empty View profile is allowed, but it is
        easy to save one by mistake. The save code uses this to show a
        neutral warning before saving anyway.
        """
        view_choices = getattr(self, 'view_profile_save_choices', {})
        if not isinstance(view_choices, dict):
            return False

        for value in view_choices.values():
            if bool(value):
                return True
        return False

    def confirm_save_empty_view_profile(self):
        """
        Ask before saving a View profile where no checkboxes are selected.
        """
        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('No checkboxes are selected for this View profile.'))
        dialog.format_secondary_text(_('Save anyway?'))
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('Save anyway'), Gtk.ResponseType.OK)
        response = dialog.run()
        dialog.destroy()
        return response == Gtk.ResponseType.OK

    def save_current_view_profile(self, _menuitem=None):
        """
        Save the current graph view back to the already loaded/saved View
        profile file.
        """
        if not self.profile_function_action_allowed():
            return

        if not self.current_view_profile_filename:
            return

        self.save_graphview_profile(
            None, 'view_profile', self.current_view_profile_filename, True)

    def delete_current_view_profile(self, _button=None):
        """
        Delete the currently loaded/saved View profile JSON file.
        """
        if not self.profile_function_action_allowed():
            return

        filename = self.current_view_profile_filename
        if not filename:
            return

        profile_name = self.current_view_profile_name
        if not profile_name:
            profile_name = os.path.splitext(os.path.basename(filename))[0]

        if not os.path.isfile(filename):
            if self.get_profile_startup_mode() == 'view':
                self.set_profile_startup_mode('none')
            self.clear_startup_view_profile()
            self.set_current_view_profile('', '')
            self.clear_view_profile_controls()
            self.sync_profile_startup_controls()
            WarningDialog(
                _('View profile file not found'),
                filename,
                parent=self.uistate.window)
            return

        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Delete current View profile?'))
        dialog.format_secondary_text(profile_name or filename)
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('_Delete'), Gtk.ResponseType.OK)

        response = dialog.run()
        dialog.destroy()

        if response != Gtk.ResponseType.OK:
            return

        try:
            os.remove(filename)
        except OSError as err:
            WarningDialog(
                _('Could not delete View profile'),
                str(err),
                parent=self.uistate.window)
            return

        # Deleting a View profile should not load or apply
        # anything else. If it was selected for startup, fall back to No
        # profile and clear the View-profile column without changing the graph.
        if self.get_profile_startup_mode() == 'view':
            self.set_profile_startup_mode('none')

        self.set_current_view_profile('', '')
        self.clear_view_profile_controls()
        self.sync_profile_startup_controls()

        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.INFO,
            buttons=Gtk.ButtonsType.OK,
            text=_('View profile deleted'))
        dialog.format_secondary_text(filename)
        dialog.run()
        dialog.destroy()

    def normalize_graphview_profile_path(self, path):
        """
        Normalize a path before comparing database identity values.
        """
        if not isinstance(path, str) or not path:
            return ''
        try:
            return os.path.normcase(os.path.abspath(os.path.expanduser(path)))
        except Exception:
            return path

    def get_graphview_profile_database_differences(self, profile):
        """
        Return saved/current family-tree values that differ.

        A changed name or path does not prove that this is another family
        tree. A Gramps backup restored into a new book can legitimately
        change all three values.
        """
        if not isinstance(profile, dict):
            return []

        current_db_name, current_media_path, current_db_path = (
            self.get_graphview_db_profile_info())

        fields = (
            (_('Family tree name'), 'db_name',
             profile.get('db_name', ''), current_db_name, False),
            (_('Database location'), 'db_internal_path',
             profile.get('db_internal_path', ''), current_db_path, True),
            (_('Media path'), 'media_path',
             profile.get('media_path', ''), current_media_path, True),
        )

        differences = []
        for label, key, saved_value, current_value, is_path in fields:
            # Missing metadata is not treated as proof of another tree.
            # Current profiles always save all three fields.
            if key not in profile:
                continue

            saved_value = saved_value if isinstance(saved_value, str) else ''
            current_value = (
                current_value if isinstance(current_value, str) else '')

            if is_path:
                saved_compare = self.normalize_graphview_profile_path(
                    saved_value)
                current_compare = self.normalize_graphview_profile_path(
                    current_value)
            else:
                saved_compare = saved_value
                current_compare = current_value

            if saved_compare != current_compare:
                differences.append({
                    'label': label,
                    'saved': saved_value,
                    'current': current_value,
                })

        return differences

    def format_graphview_profile_database_differences(self, differences):
        """Return readable saved/current family-tree differences."""
        lines = []
        empty_text = _('(not set)')

        for difference in differences:
            label = difference.get('label', '')
            saved_value = difference.get('saved', '') or empty_text
            current_value = difference.get('current', '') or empty_text
            lines.extend([
                '%s:' % label,
                '%s: %s' % (_('Profile'), saved_value),
                '%s: %s' % (_('Current'), current_value),
                '',
            ])

        return '\n'.join(lines).rstrip()

    def confirm_graphview_profile_database_context(self, profile,
                                                   profile_type):
        """
        Check family-tree metadata before any profile values are applied.

        Standard profiles:
        changed tree information gives one Cancel/Load anyway dialog.

        View profiles:
        changed information plus matching saved people is treated as a likely
        restored/moved copy; changed information plus an unresolved saved
        person blocks loading as a likely profile from another family tree.
        """
        differences = self.get_graphview_profile_database_differences(profile)
        if not differences:
            return True

        difference_text = (
            self.format_graphview_profile_database_differences(differences))

        if profile_type == 'view_profile':
            missing_people = []
            verified_people = []

            for role_name, key in (
                    (_('Home person'), 'home_person'),
                    (_('Active person'), 'active_person')):
                person_data = profile.get(key, {})
                if not isinstance(person_data, dict) or not person_data:
                    continue

                _handle, person = self.resolve_graphview_profile_person_data(
                    person_data)
                description = self.get_saved_profile_person_description(
                    role_name, person_data)

                if person:
                    verified_people.append(description)
                else:
                    missing_people.append(description)

            if missing_people:
                detail = _(
                    'This View profile appears to belong to another family '
                    'tree.')
                detail += '\n\n' + _(
                    'The family tree information is different:')
                detail += '\n\n' + difference_text
                detail += '\n\n' + _(
                    'These saved people could not be found in the current '
                    'family tree:')
                detail += '\n\n' + '\n'.join(missing_people)
                detail += '\n\n' + _('The profile was not loaded.')

                WarningDialog(
                    _('View profile belongs to another family tree'),
                    detail,
                    parent=self.uistate.window)
                return False

            dialog = Gtk.MessageDialog(
                transient_for=self.uistate.window,
                modal=True,
                message_type=Gtk.MessageType.QUESTION,
                buttons=Gtk.ButtonsType.NONE,
                text=_('Family tree information is different'))

            detail = _(
                'This View profile was saved with different family tree '
                'information:')
            detail += '\n\n' + difference_text

            if verified_people:
                detail += '\n\n' + _(
                    'The saved people were found in the current family '
                    'tree:')
                detail += '\n\n' + '\n'.join(verified_people)
            else:
                detail += '\n\n' + _(
                    'This profile does not contain saved Home or Active '
                    'persons that can be checked.')

            detail += '\n\n' + _(
                'This may be a restored or moved copy of the same family '
                'tree. If this is the correct tree, load the profile and '
                'save it again for the current family tree.')

            dialog.format_secondary_text(detail)
            dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
            dialog.add_button(_('Load anyway'), Gtk.ResponseType.OK)

            response = dialog.run()
            dialog.destroy()
            return response == Gtk.ResponseType.OK

        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Family tree information is different'))

        detail = _(
            'This Standard profile was saved with different family tree '
            'information:')
        detail += '\n\n' + difference_text
        detail += '\n\n' + _(
            'This may be a restored or moved copy of the same family tree. '
            'If this is the correct tree, load the profile and save it again '
            'for the current family tree.')

        dialog.format_secondary_text(detail)
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('Load anyway'), Gtk.ResponseType.OK)

        response = dialog.run()
        dialog.destroy()
        return response == Gtk.ResponseType.OK

    def resolve_graphview_profile_person_data(self, person_data):
        """
        Resolve a saved View-profile person safely in the open database.

        A restored database can change internal handles while preserving
        Gramps IDs. Never accept a handle that now points to a person with a
        different saved Gramps ID; fall back to an ID lookup instead.
        """
        if not isinstance(person_data, dict) or not person_data:
            return '', None

        person = None
        handle = person_data.get('handle', '') or ''
        gramps_id = person_data.get('gramps_id', '') or ''

        if handle:
            try:
                person = self.dbstate.db.get_person_from_handle(handle)
            except Exception:
                person = None

            if person and gramps_id:
                try:
                    if person.get_gramps_id() != gramps_id:
                        person = None
                except Exception:
                    person = None

        if not person and gramps_id and hasattr(
                self.dbstate.db, 'get_person_from_gramps_id'):
            try:
                person = self.dbstate.db.get_person_from_gramps_id(gramps_id)
            except Exception:
                person = None

            if person:
                try:
                    handle = person.get_handle()
                except Exception:
                    handle = ''

        return handle, person

    def get_saved_profile_person_description(self, role_name, person_data):
        """
        Return a readable Home/Active person line for missing-person dialogs.
        """
        name = ''
        gramps_id = ''

        if isinstance(person_data, dict):
            name = person_data.get('name', '') or ''
            gramps_id = person_data.get('gramps_id', '') or ''
            handle = person_data.get('handle', '') or ''
        else:
            handle = ''

        description = name.strip() if isinstance(name, str) else ''

        if gramps_id:
            if description:
                description = '%s (%s)' % (description, gramps_id)
            else:
                description = gramps_id

        if not description and handle:
            description = handle

        if not description:
            description = _('(unknown name)')

        return '%s: %s' % (role_name, description)

    def ask_load_view_profile_with_missing_persons(self, missing_people):
        """
        Ask whether a View profile should load when saved Home/Active person
        choices cannot be found in the open database.
        """
        if not missing_people:
            return True

        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Home or Active person not found'))

        detail = _(
            'These saved people were not found in this family tree:')
        detail += '\n\n' + '\n'.join(missing_people)
        detail += '\n\n' + _(
            'Load anyway without them?')

        dialog.format_secondary_text(detail)
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('Load'), Gtk.ResponseType.OK)

        response = dialog.run()
        dialog.destroy()
        return response == Gtk.ResponseType.OK

    def apply_profile_media_path(self, profile, show_warning=False):
        """
        Restore the family-tree media path saved in a Graph View profile.

        This only changes the Gramps database media path if Gramps exposes a
        safe set_mediapath() method and the saved folder still exists.
        """
        if not isinstance(profile, dict):
            return False

        media_path = profile.get('media_path', '')
        if not isinstance(media_path, str) or not media_path:
            return True

        media_path = os.path.abspath(os.path.expanduser(media_path))
        if not os.path.isdir(media_path):
            if show_warning:
                WarningDialog(
                    _('Graph View profile media path not found'),
                    _('The saved media path does not exist:\n%s') % media_path,
                    parent=self.uistate.window)
            return False

        try:
            current_media_path = self.dbstate.db.get_mediapath() or ''
        except Exception:
            current_media_path = ''

        try:
            current_media_path = os.path.abspath(
                os.path.expanduser(current_media_path))
        except Exception:
            current_media_path = current_media_path or ''

        if current_media_path == media_path:
            return True

        set_mediapath = getattr(self.dbstate.db, 'set_mediapath', None)
        if not callable(set_mediapath):
            if show_warning:
                WarningDialog(
                    _('Graph View profile media path not restored'),
                    _('This Gramps database does not support set_mediapath().'),
                    parent=self.uistate.window)
            return False

        try:
            set_mediapath(media_path)
        except Exception as msg:
            if show_warning:
                WarningDialog(
                    _('Graph View profile media path not restored'),
                    str(msg),
                    parent=self.uistate.window)
            return False

        return True

    def find_people_limit_config_spinner(self, container=None):
        """
        Return the Limit number displayed spinner from the open Configure
        dialog, if it exists.

        Gramps' ConfigureDialog helper owns the normal config binding. When
        a profile is loaded while Configure is already open, the config value
        changes correctly, but the visible spin button can keep its old value
        until the dialog is rebuilt. This helper lets profile loads refresh
        that one visible widget.
        """
        widget = getattr(self, 'people_limit_config_spinner', None)
        if isinstance(widget, Gtk.SpinButton):
            try:
                if widget.get_parent() is not None:
                    return widget
            except Exception:
                pass

        if container is None:
            return None

        try:
            children = container.get_children()
        except Exception:
            return None

        for child in children:
            if isinstance(child, Gtk.SpinButton):
                self.people_limit_config_spinner = child
                return child

            found = self.find_people_limit_config_spinner(child)
            if found is not None:
                return found

        return None

    def remember_people_limit_config_spinner(self, widget_or_container=None):
        """
        Remember the Limit number displayed spin button, if ConfigureDialog
        exposes it or if it can be found in the Layout grid.
        """
        widget = widget_or_container

        if isinstance(widget, (list, tuple)):
            for item in widget:
                if isinstance(item, Gtk.SpinButton):
                    self.people_limit_config_spinner = item
                    return item
                found = self.find_people_limit_config_spinner(item)
                if found is not None:
                    return found
            return None

        if isinstance(widget, Gtk.SpinButton):
            self.people_limit_config_spinner = widget
            return widget

        found = self.find_people_limit_config_spinner(widget)
        if found is not None:
            return found

        return None

    def sync_people_limit_config_spinner(self):
        """
        Refresh the visible Limit number displayed value while Configure is
        open. Safe to call when Configure is closed.
        """
        spinner = self.find_people_limit_config_spinner()
        if spinner is None:
            return

        try:
            value = int(self._config.get('interface.graphview-people-limit'))
        except Exception:
            value = 0

        try:
            if int(spinner.get_value()) != value:
                spinner.set_value(value)
        except Exception:
            pass

    def set_open_config_widget_without_callback(self, widget, callback,
                                                setter):
        """
        Change a visible Configure widget without writing the same value back
        through ConfigureDialog and starting another Graph View redraw.
        """
        if widget is None:
            return

        try:
            if widget.get_parent() is None:
                return
        except Exception:
            return

        callback_blocked = False
        if callback is not None:
            try:
                widget.handler_block_by_func(callback)
                callback_blocked = True
            except Exception:
                callback_blocked = False

        try:
            setter()
        except Exception:
            pass
        finally:
            if callback_blocked:
                try:
                    widget.handler_unblock_by_func(callback)
                except Exception:
                    pass

    def sync_open_layout_and_theme_widgets(self):
        """
        Refresh all profile-controlled fields shown on the ordinary Layout
        and Themes pages while Configure remains open.

        This is display synchronization only. The profile load has already
        written the new values to Graph View config.
        """
        widgets = getattr(self, 'open_config_widgets', {})
        if not isinstance(widgets, dict) or not widgets:
            return

        configdialog = getattr(self, 'open_graphview_configdialog', None)
        checkbox_callback = getattr(configdialog, 'update_checkbox', None)
        combo_callback = getattr(configdialog, 'update_combo', None)
        color_callback = getattr(configdialog, 'update_color', None)
        spinner_callback = getattr(configdialog, 'update_spinner', None)

        checkbox_keys = (
            'interface.graphview-show-images',
            'interface.graphview-show-id',
            'interface.graphview-show-avatars',
            'interface.graphview-highlight-home-person',
            'interface.graphview-show-full-dates',
            'interface.graphview-show-places',
            'interface.graphview-show-tags',
            'interface.graphview-filter-family-tag',
        )
        for config_key in checkbox_keys:
            widget = widgets.get(config_key)
            if not isinstance(widget, Gtk.CheckButton):
                continue
            try:
                value = bool(self._config.get(config_key))
                if widget.get_active() != value:
                    self.set_open_config_widget_without_callback(
                        widget, checkbox_callback,
                        lambda widget=widget, value=value:
                            widget.set_active(value))
            except Exception:
                pass

        combo_keys = (
            'interface.graphview-place-format',
            'interface.graphview-direction',
            'interface.graphview-person-theme',
            'interface.graphview-avatars-style',
        )
        for config_key in combo_keys:
            widget = widgets.get(config_key)
            if not isinstance(widget, Gtk.ComboBox):
                continue
            try:
                value = int(self._config.get(config_key))
                if widget.get_active() != value:
                    self.set_open_config_widget_without_callback(
                        widget, combo_callback,
                        lambda widget=widget, value=value:
                            widget.set_active(value))
            except Exception:
                pass

        spinner_keys = (
            'interface.graphview-people-limit',
            'interface.graphview-active-person-border-size',
            'interface.graphview-person-border-size',
        )
        for config_key in spinner_keys:
            widget = widgets.get(config_key)
            if not isinstance(widget, Gtk.SpinButton):
                continue
            try:
                value = int(self._config.get(config_key))
                if int(widget.get_value()) != value:
                    self.set_open_config_widget_without_callback(
                        widget, spinner_callback,
                        lambda widget=widget, value=value:
                            widget.set_value(value))
            except Exception:
                pass

        color_key = 'interface.graphview-home-path-color'
        color_widget = widgets.get(color_key)
        if isinstance(color_widget, Gtk.ColorButton):
            try:
                color_value = str(self._config.get(color_key))
                rgba = Gdk.RGBA()
                if rgba.parse(color_value):
                    self.set_open_config_widget_without_callback(
                        color_widget, color_callback,
                        lambda: color_widget.set_rgba(rgba))
                    color_label = getattr(
                        self, 'home_path_color_config_label', None)
                    if color_label is not None:
                        color_label.set_text(color_value)
            except Exception:
                pass

        font_key = 'interface.graphview-font'
        font_widget = widgets.get(font_key)
        if isinstance(font_widget, Gtk.FontButton):
            try:
                font = self._config.get(font_key)
                font_string = '%s, %d' % (font[0], int(font[1]))

                def set_font_button_value():
                    if hasattr(font_widget, 'set_font'):
                        font_widget.set_font(font_string)
                    else:
                        font_widget.set_font_name(font_string)

                self.set_open_config_widget_without_callback(
                    font_widget, self.config_change_font,
                    set_font_button_value)
            except Exception:
                pass

        avatar_file_callbacks = {
            'interface.graphview-avatars-male': self.cb_male_avatar_set,
            'interface.graphview-avatars-female': self.cb_female_avatar_set,
            'interface.graphview-avatars-unknown': self.cb_unknown_avatar_set,
            'interface.graphview-avatars-other': self.cb_other_avatar_set,
        }
        for config_key, callback in avatar_file_callbacks.items():
            widget = widgets.get(config_key)
            if not isinstance(widget, Gtk.FileChooserButton):
                continue
            try:
                filename = self._config.get(config_key) or ''
                current_filename = widget.get_filename() or ''
                if current_filename == filename:
                    continue

                def set_avatar_filename(widget=widget, filename=filename):
                    if filename:
                        widget.set_filename(filename)
                    else:
                        widget.unselect_all()

                self.set_open_config_widget_without_callback(
                    widget, callback, set_avatar_filename)
            except Exception:
                pass

        # Keep custom-avatar rows in step with the loaded avatar style.
        try:
            custom_avatars_visible = (
                int(self._config.get('interface.graphview-avatars-style')) == 0)
            for widget in self.avatar_widgets:
                widget.set_visible(custom_avatars_visible)
        except Exception:
            pass

    def sync_open_config_widgets_after_profile_load(self):
        """
        Refresh visible Configure widgets that do not update automatically
        when profile loading changes config values behind an already-open
        Configure dialog.
        """
        self.sync_open_layout_and_theme_widgets()
        self.sync_people_limit_config_spinner()

    @batch_profile_graph_refresh(redraw_after=True)
    def apply_standard_graphview_profile(self, profile):
        """
        Apply layout/display/style from a standard profile.
        """
        if not isinstance(profile, dict):
            return False

        if profile.get('profile_version') != 1:
            return False

        profile_type = profile.get('profile_type', '')
        if profile_type != 'standard_profile':
            return False

        # Database name/path values are informative, not
        # a hard lock. A Gramps backup restored into a new family tree can
        # have the same people and settings but a new db_name/db_internal_path.
        # media_path is also treated as profile information, not as a setting
        # that should silently change the open database media path.

        allowed_config_keys = [
            'interface.graphview-direction',
            'interface.graphview-show-lines',
            'interface.graphview-ranksep',
            'interface.graphview-nodesep',
            'interface.graphview-ancestor-generations',
            'interface.graphview-descendant-generations',
            'interface.graphview-show-all-connected',
            'interface.graphview-people-limit',
            'interface.graphview-show-images',
            'interface.graphview-show-id',
            'interface.graphview-show-avatars',
            'interface.graphview-show-full-dates',
            'interface.graphview-show-places',
            'interface.graphview-place-format',
            'interface.graphview-show-tags',
            'interface.graphview-filter-family-tag',
            'interface.graphview-highlight-home-person',
            'interface.graphview-home-path-color',
            'interface.graphview-person-theme',
            'interface.graphview-font',
            'interface.graphview-avatars-style',
            'interface.graphview-person-border-size',
            'interface.graphview-active-person-border-size',
            'interface.graphview-avatars-male',
            'interface.graphview-avatars-female',
            'interface.graphview-avatars-unknown',
            'interface.graphview-avatars-other',
        ]

        loaded_values = {}
        for section_name in ('content', 'layout', 'display', 'style'):
            section = profile.get(section_name, {})
            if isinstance(section, dict):
                loaded_values.update(section)

        self.apply_avatar_profile_load_rules(loaded_values)
        self.apply_profile_people_limit_load_rule(profile, loaded_values)

        # Failure to save the temporary restore point may
        # disable temporary use, but it must never block this profile or the
        # final graph rebuild.
        self.prepare_temporary_profile_restore_snapshot_before_load()

        # A Standard profile does not save Home person or
        # Active person. Always return to the current book's Home person
        # before applying it, so a previously loaded View profile cannot
        # leave the graph centred on a different Active person.
        try:
            home_person = self.dbstate.db.get_default_person()
        except Exception:
            home_person = None

        if home_person is not None:
            try:
                home_handle = home_person.get_handle() or ''
            except Exception:
                home_handle = ''

            try:
                active_handle = self.get_active() or ''
            except Exception:
                active_handle = ''

            if home_handle and active_handle != home_handle:
                self.change_active(home_handle)

        if (loaded_values.get('interface.graphview-filter-family-tag') and
                not self.family_tag_filter_value_is_allowed(True)):
            loaded_values['interface.graphview-filter-family-tag'] = False

        self.set_profile_config_values_all_connected_last(
            allowed_config_keys, loaded_values)

        self.temporary_profile_restore_profile_loaded = True

        # The config value is changed now, but an already-open
        # Configure/Layout page may still show the old spin-button value.
        self.sync_open_config_widgets_after_profile_load()

        # Keep the Profiles page checkboxes in sync when the Configure
        # dialog is open while a Standard profile is loaded.
        self.standard_profile_controls_active = True
        self.sync_standard_profile_controls()

        view_state = profile.get('view_state_optional', {})

        active_handle = self.get_active()
        if self.graph_widget and active_handle:
            self.graph_widget.populate(active_handle)
            if hasattr(self.graph_widget, 'sync_profile_controls'):
                GLib.idle_add(self.graph_widget.sync_profile_controls)
            if (isinstance(view_state, dict) and view_state and
                    hasattr(self.graph_widget, 'restore_profile_view_state')):
                GLib.timeout_add(
                    200, self.graph_widget.restore_profile_view_state,
                    view_state)

        return True

    def is_standard_profile_context_ready(self):
        """
        Return True only when Graph View has a real open database and person.
        Gramps can construct the view before a family tree is fully open, so
        startup profile loading must not run during early startup.
        """
        if not self.graph_widget:
            return False

        if not self.active:
            return False

        try:
            active_handle = self.get_active()
        except Exception:
            return False

        if not active_handle:
            return False

        try:
            person = self.dbstate.db.get_person_from_handle(active_handle)
        except Exception:
            return False

        if person is None:
            return False

        db_name, _media_path, db_internal_path = self.get_graphview_db_profile_info()
        if not db_name:
            return False

        if not db_internal_path:
            return False

        return True

    def schedule_auto_load_standard_profile(self):
        """
        Schedule automatic standard-profile handling after a real populate.

        A large graph can still be drawing on screen just after populate() has
        returned. A short timeout lets GTK finish painting before a possible
        standard-profile redraw is started.
        """
        if not self.profile_function_is_enabled():
            return

        if self.get_profile_startup_mode() == 'none':
            return

        if self.standard_profile_auto_checked:
            return

        if self.standard_profile_auto_scheduled:
            return

        self.standard_profile_auto_scheduled = True
        GLib.timeout_add(2500, self.delayed_auto_load_standard_profile)

    def delayed_auto_load_standard_profile(self):
        """
        Run automatic startup-profile handling after the fallback delay.

        Returning False always removes this one-shot GLib timeout.
        """
        self.standard_profile_auto_scheduled = False
        self.auto_load_or_offer_standard_profile()
        return False

    def auto_load_or_offer_standard_profile(self):
        """
        Load the configured startup profile when the real book context is ready.

        Return True only when a valid Standard/View startup profile was
        applied. The caller can then skip GraphView's ordinary
        first populate(), because the profile loader already rebuilt the graph.
        """
        if self.standard_profile_auto_checked:
            return bool(self.startup_profile_created_initial_graph)

        if not self.profile_function_is_enabled():
            return False

        if not self.is_standard_profile_context_ready():
            return False

        startup_mode = self.get_profile_startup_mode()
        if startup_mode == 'none':
            return False

        self.standard_profile_auto_checked = True
        loaded = False

        if startup_mode == 'standard':
            filename = self.get_standard_profile_filename()

            # A saved Standard profile is required at startup.
            if not os.path.isfile(filename):
                return False

            try:
                with open(filename, 'r', encoding='utf-8') as json_file:
                    profile = json.load(json_file)

                if not self.confirm_graphview_profile_database_context(
                        profile, 'standard_profile'):
                    return False

                loaded = bool(self.apply_standard_graphview_profile(profile))
                if loaded:
                    self.update_profiles_status_labels()
            except (OSError, json.JSONDecodeError):
                loaded = False

        elif startup_mode == 'view':
            filename = (self.current_view_profile_filename or
                        self.get_startup_view_profile_filename())

            if not filename or not os.path.isfile(filename):
                return False

            loaded = bool(self.load_graphview_profile_from_filename(
                filename, startup_load=True))

        if loaded:
            self.startup_profile_created_initial_graph = True
            self.standard_profile_auto_scheduled = False

        return loaded

    def standard_profile_database_context_ready(self):
        """
        Return True when the current family-tree identity is known well enough
        to decide whether its Standard profile file exists.

        During Gramps startup the Profiles page/status can be synced before
        the open database has supplied its real name/path. In that state we
        must not change a saved startup choice from Standard profile to
        No profile just because the real Standard-profile filename cannot yet
        be resolved.
        """
        try:
            db_name, _media_path, db_internal_path = (
                self.get_graphview_db_profile_info())
        except Exception:
            return False

        return bool(db_name and db_internal_path)

    def standard_graphview_profile_exists(self):
        """
        Return True if this family tree has a saved Standard profile.
        """
        if not self.standard_profile_database_context_ready():
            return False
        try:
            filename = self.get_standard_profile_filename()
        except Exception:
            return False
        return os.path.isfile(filename)

    def delete_standard_graphview_profile(self, _button=None):
        """
        Delete this family tree's saved Standard profile.
        """
        if not self.profile_function_action_allowed():
            return

        filename = self.get_standard_profile_filename()

        if not os.path.isfile(filename):
            WarningDialog(
                _('No standard profile'),
                _('There is no standard Graph View profile to delete for this family tree.'),
                parent=self.uistate.window)
            return

        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Delete standard profile?'))
        dialog.format_secondary_text(
            _('This deletes the standard Graph View profile for the open family tree.'))
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('_Delete'), Gtk.ResponseType.OK)

        response = dialog.run()
        dialog.destroy()

        if response != Gtk.ResponseType.OK:
            return

        try:
            os.remove(filename)
        except OSError as err:
            WarningDialog(
                _('Could not delete standard profile'),
                str(err),
                parent=self.uistate.window)
            return

        # Deleting a Standard profile should not load or
        # apply anything else. If it was selected for startup, fall back to
        # No profile and clear the Standard-profile column without changing
        # the graph.
        if self.get_profile_startup_mode() == 'standard':
            self.set_profile_startup_mode('none')

        self.standard_profile_controls_active = False
        self.clear_standard_profile_controls()
        self.sync_profile_startup_controls()

        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.INFO,
            buttons=Gtk.ButtonsType.OK,
            text=_('Standard profile deleted'))
        dialog.format_secondary_text(filename)
        dialog.run()
        dialog.destroy()

        self.update_profiles_status_labels()

    def choose_graphview_profile_type(self):
        """
        Ask which kind of profile should be saved.
        Returns 'view_profile', 'standard_profile', or None if cancelled.
        """
        if not self.profile_function_action_allowed():
            return None

        dialog = Gtk.MessageDialog(
            transient_for=self.uistate.window,
            modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.NONE,
            text=_('Choose profile type'))
        dialog.format_secondary_text(
            _('A View profile saves the complete graph view.\n'
              'A Standard profile saves layout, display and style settings '
              'for the open family tree.'))
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('Standard profile'), 1)
        dialog.add_button(_('View profile'), 2)

        response = dialog.run()
        dialog.destroy()

        if response == 1:
            return 'standard_profile'
        if response == 2:
            return 'view_profile'
        return None

    def save_graphview_profile(self, _menuitem=None, profile_type=None,
                                target_filename=None, confirm_overwrite=False,
                                save_all_supported=False):
        """
        Save a Graph View profile as JSON.
        View profiles save the full view and ask for filename unless a target
        filename is supplied. Standard profiles save layout/display/style
        automatically per family tree.
        """
        if not self.profile_function_action_allowed():
            return

        if profile_type is None:
            profile_type = self.choose_graphview_profile_type()
        if profile_type is None:
            return

        active_handle = self.get_active()
        person = None
        if active_handle:
            person = self.dbstate.db.get_person_from_handle(active_handle)

        if profile_type == 'view_profile' and not person:
            WarningDialog(
                _('No active person'),
                _('A Graph View profile needs an active person.'),
                parent=self.uistate.window)
            return

        if (profile_type == 'view_profile' and
                not save_all_supported and
                not self.view_profile_has_selected_choices()):
            if not self.confirm_save_empty_view_profile():
                return

        home_person = self.dbstate.db.get_default_person()
        home_handle = home_person.get_handle() if home_person else ''
        db_name, media_path, db_internal_path = self.get_graphview_db_profile_info()

        def get_config_value(config_key):
            """Read a Graph View config value."""
            return self._config.get(config_key)

        display_section = {
            "interface.graphview-show-images": get_config_value(
                "interface.graphview-show-images"),
            "interface.graphview-show-id": get_config_value(
                "interface.graphview-show-id"),
            "interface.graphview-show-avatars": get_config_value(
                "interface.graphview-show-avatars"),
            "interface.graphview-show-full-dates": get_config_value(
                "interface.graphview-show-full-dates"),
            "interface.graphview-show-places": get_config_value(
                "interface.graphview-show-places"),
            "interface.graphview-place-format": get_config_value(
                "interface.graphview-place-format"),
            "interface.graphview-show-tags": get_config_value(
                "interface.graphview-show-tags"),
        }

        style_section = {
            "interface.graphview-highlight-home-person": get_config_value(
                "interface.graphview-highlight-home-person"),
            "interface.graphview-home-path-color": get_config_value(
                "interface.graphview-home-path-color"),
            "interface.graphview-person-theme": get_config_value(
                "interface.graphview-person-theme"),
            "interface.graphview-font": get_config_value(
                "interface.graphview-font"),
            "interface.graphview-avatars-style": get_config_value(
                "interface.graphview-avatars-style"),
            "interface.graphview-person-border-size": get_config_value(
                "interface.graphview-person-border-size"),
            "interface.graphview-active-person-border-size": get_config_value(
                "interface.graphview-active-person-border-size"),
            "interface.graphview-avatars-male": get_config_value(
                "interface.graphview-avatars-male"),
            "interface.graphview-avatars-female": get_config_value(
                "interface.graphview-avatars-female"),
            "interface.graphview-avatars-unknown": get_config_value(
                "interface.graphview-avatars-unknown"),
            "interface.graphview-avatars-other": get_config_value(
                "interface.graphview-avatars-other"),
        }

        layout_section = {
            "interface.graphview-direction": get_config_value(
                "interface.graphview-direction"),
            "interface.graphview-show-lines": get_config_value(
                "interface.graphview-show-lines"),
            "interface.graphview-ranksep": get_config_value(
                "interface.graphview-ranksep"),
            "interface.graphview-nodesep": get_config_value(
                "interface.graphview-nodesep"),
        }

        profile = {
            "profile_version": 1,
            "profile_name": "",
            "profile_type": profile_type,
            "created_at": datetime.now().isoformat(timespec="seconds"),
            "db_name": db_name,
            "media_path": media_path,
            "db_internal_path": db_internal_path,
            "layout": layout_section,
            "display": display_section,
            "style": style_section,
        }

        if profile_type == 'view_profile':
            if save_all_supported:
                view_choices = self.get_full_current_view_profile_choices()
            else:
                view_choices = getattr(
                    self, 'view_profile_save_choices', {})
            save_active_person = view_choices.get('active_person', False)
            save_home_person = view_choices.get('home_person', False)
            save_time_direction = view_choices.get('time_direction', False)
            save_people_limit = view_choices.get('people_limit', False)
            save_theme = view_choices.get('theme', False)
            save_path_color = view_choices.get('path_color', False)
            save_font = view_choices.get('font', False)
            save_active_person_border_size = view_choices.get(
                'active_person_border_size', False)
            save_person_border_size = view_choices.get(
                'person_border_size', False)
            save_line_types = view_choices.get('line_types', False)
            save_generations = view_choices.get('generations', False)
            save_spacings = view_choices.get('spacings', False)
            save_view_state = view_choices.get('view_state', False)

            # Boolean View-profile rows are also taken from
            # the View column choices, not from whatever GraphView currently
            # happens to show when no View profile is active.
            for config_key in (
                    'interface.graphview-show-images',
                    'interface.graphview-show-id',
                    'interface.graphview-show-avatars',
                    'interface.graphview-show-full-dates',
                    'interface.graphview-show-places',
                    'interface.graphview-show-tags'):
                display_section[config_key] = bool(
                    view_choices.get(config_key, False))
            style_section['interface.graphview-highlight-home-person'] = bool(
                view_choices.get(
                    'interface.graphview-highlight-home-person', False))

            # Time direction in View profile is an
            # include/exclude choice. When unchecked, the value is removed
            # from JSON and therefore not applied when the profile is loaded.
            if not save_time_direction:
                layout_section.pop('interface.graphview-direction', None)

            # Line types follow the same include/exclude
            # model in View profile.
            if not save_line_types:
                layout_section.pop('interface.graphview-show-lines', None)

            # Spacings is one include/exclude choice for
            # rank separation and node separation.
            if not save_spacings:
                layout_section.pop('interface.graphview-ranksep', None)
                layout_section.pop('interface.graphview-nodesep', None)

            profile.update({
                "content": {
                    "interface.graphview-ancestor-generations": get_config_value(
                        "interface.graphview-ancestor-generations"),
                    "interface.graphview-descendant-generations": get_config_value(
                        "interface.graphview-descendant-generations"),
                    "interface.graphview-show-all-connected": get_config_value(
                        "interface.graphview-show-all-connected"),
                    "interface.graphview-filter-family-tag": get_config_value(
                        "interface.graphview-filter-family-tag"),
                    "interface.graphview-people-limit": get_config_value(
                        "interface.graphview-people-limit"),
                },
                "view_state_optional": {
                    "interface.graphview-scale": (
                        self.graph_widget.scale if self.graph_widget else None),
                    "horizontal_adjustment_value": (
                        self.graph_widget.hadjustment.get_value()
                        if self.graph_widget else None),
                    "vertical_adjustment_value": (
                        self.graph_widget.vadjustment.get_value()
                        if self.graph_widget else None),
                },
            })

            profile['content']['interface.graphview-show-all-connected'] = bool(
                view_choices.get(
                    'interface.graphview-show-all-connected', False))
            filter_value = bool(
                view_choices.get(
                    'interface.graphview-filter-family-tag', False))
            if (filter_value and
                    not self.family_tag_filter_value_is_allowed(True)):
                filter_value = False
            profile['content']['interface.graphview-filter-family-tag'] = filter_value

            # Zoom & chart position is saved/restored only
            # when selected. When unchecked, the whole optional view-state
            # section is removed from the View profile JSON.
            if not save_view_state:
                profile.pop('view_state_optional', None)

            # Always save the numeric value, including
            # 0 = unlimited. A separate flag preserves whether a positive
            # value was selected for profile load.
            self.set_profile_people_limit_choice(
                profile, save_people_limit,
                get_config_value('interface.graphview-people-limit'))

            # Generations in View profile is one
            # include/exclude choice for two JSON values. When unchecked,
            # both generation values are removed from the content section.
            if not save_generations:
                profile['content'].pop(
                    'interface.graphview-ancestor-generations', None)
                profile['content'].pop(
                    'interface.graphview-descendant-generations', None)

            # Theme, Path color to home person and Font in
            # View profile follow the same include/exclude model as
            # Time direction. When unchecked, the style value is removed
            # from JSON and therefore not applied when the profile is loaded.
            if not save_theme:
                profile['style'].pop(
                    'interface.graphview-person-theme', None)
            if not save_path_color:
                profile['style'].pop(
                    'interface.graphview-home-path-color', None)
            if not save_font:
                profile['style'].pop(
                    'interface.graphview-font', None)

            # Active person border size follows the same
            # include/exclude model in View profile.
            if not save_active_person_border_size:
                profile['style'].pop(
                    'interface.graphview-active-person-border-size', None)

            # Person border size follows the same
            # include/exclude model in View profile.
            if not save_person_border_size:
                profile['style'].pop(
                    'interface.graphview-person-border-size', None)

            if save_active_person:
                profile["active_person"] = {
                    "handle": active_handle,
                    "gramps_id": person.get_gramps_id(),
                    "name": displayer.display(person),
                }

            if save_home_person:
                profile["home_person"] = {
                    "handle": home_handle,
                    "gramps_id": (home_person.get_gramps_id()
                                  if home_person else ''),
                    "name": (displayer.display(home_person)
                             if home_person else ''),
                }


        if profile_type == 'view_profile':
            profile = self.apply_avatar_profile_save_rules(profile)

        if profile_type == 'standard_profile':
            if self.save_standard_graphview_profile(show_message=True):
                self.clear_profiles_page_unsaved()
            self.update_profiles_status_labels()
            return

        if target_filename:
            filename = target_filename
            if confirm_overwrite:
                if not self.confirm_overwrite_current_view_profile():
                    return
            profile_name = os.path.splitext(os.path.basename(filename))[0]
            profile["profile_name"] = profile_name
            try:
                with open(filename, 'w', encoding='utf-8') as json_file:
                    json.dump(profile, json_file, ensure_ascii=False, indent=2)
                self.set_current_view_profile(filename, profile_name)
                if save_all_supported:
                    self.view_profile_save_choices = dict(view_choices)
                    self.sync_view_profile_controls()
                self.clear_profiles_page_unsaved()
            except OSError as msg:
                ErrorDialog(
                    _('Could not save Graph View profile'),
                    str(msg),
                    parent=self.uistate.window)
                return
            return

        dialog = Gtk.FileChooserDialog(
            title=_('Save Graph View profile'),
            action=Gtk.FileChooserAction.SAVE,
            transient_for=self.uistate.window)
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('_Save'), Gtk.ResponseType.OK)
        dialog.set_do_overwrite_confirmation(True)

        if media_path and os.path.isdir(media_path):
            dialog.set_current_folder(media_path)
        else:
            mpath = config.get('paths.report-directory')
            if mpath:
                dialog.set_current_folder(os.path.dirname(mpath))

        dialog.set_current_name("graphview-view-profile.json")

        json_filter = Gtk.FileFilter()
        json_filter.set_name(_('JSON files'))
        json_filter.add_pattern("*.json")
        dialog.add_filter(json_filter)

        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            if not filename.lower().endswith('.json'):
                filename += '.json'

            profile_name = os.path.splitext(os.path.basename(filename))[0]
            profile["profile_name"] = profile_name

            try:
                with open(filename, 'w', encoding='utf-8') as json_file:
                    json.dump(profile, json_file, ensure_ascii=False, indent=2)
                self.set_current_view_profile(filename, profile_name)
                if save_all_supported:
                    self.view_profile_save_choices = dict(view_choices)
                    self.sync_view_profile_controls()
                self.clear_profiles_page_unsaved()
            except OSError as msg:
                ErrorDialog(
                    _('Could not save Graph View profile'),
                    str(msg),
                    parent=dialog)

        dialog.destroy()

    @batch_profile_graph_refresh(redraw_after=True)
    def load_graphview_profile_from_filename(self, filename, startup_load=False):
        """
        Load a View profile from a known JSON filename.
        Used both by manual View loading and View-profile startup loading.
        """
        try:
            with open(filename, 'r', encoding='utf-8') as json_file:
                profile = json.load(json_file)
        except (OSError, json.JSONDecodeError) as msg:
            if not startup_load:
                ErrorDialog(
                    _('Could not load Graph View profile'),
                    str(msg),
                    parent=self.uistate.window)
            return False

        if not isinstance(profile, dict):
            if not startup_load:
                WarningDialog(
                    _('Invalid Graph View profile'),
                    _('The selected file is not a Graph View profile.'),
                    parent=self.uistate.window)
            return False

        if profile.get('profile_version') != 1:
            if not startup_load:
                WarningDialog(
                    _('Unsupported Graph View profile'),
                    _('Only profile_version 1 is supported.'),
                    parent=self.uistate.window)
            return False

        profile_type = profile.get('profile_type', '')
        if profile_type != 'view_profile':
            if not startup_load:
                WarningDialog(
                    _('Invalid View profile'),
                    _('The selected file is not a View profile. Only files '
                      'with profile_type "view_profile" can be loaded here.'),
                    parent=self.uistate.window)
            return False

        # View profiles combine family-tree metadata with saved person IDs.
        # This check happens before snapshots, config values or people change.
        if not self.confirm_graphview_profile_database_context(
                profile, 'view_profile'):
            return False

        active_person = profile.get('active_person', {})
        has_active_person = (
            isinstance(active_person, dict) and bool(active_person))
        active_handle = ''
        person = None

        home_person_data = profile.get('home_person', {})
        has_home_person = (
            isinstance(home_person_data, dict) and bool(home_person_data))
        home_handle = ''
        home_person = None

        profile_for_control_sync = profile
        missing_people = []

        if has_active_person:
            active_handle, person = self.resolve_graphview_profile_person_data(
                active_person)
            if not person:
                missing_people.append(
                    self.get_saved_profile_person_description(
                        _('Active person'), active_person))
        else:
            try:
                active_handle = self.get_active()
            except Exception:
                active_handle = ''

        if has_home_person:
            home_handle, home_person = (
                self.resolve_graphview_profile_person_data(home_person_data))
            if not home_person:
                missing_people.append(
                    self.get_saved_profile_person_description(
                        _('Home person'), home_person_data))

        # With matching family-tree metadata, a person may simply have been
        # deleted later. Keep the existing one-dialog choice to load the rest.
        if missing_people:
            if not self.ask_load_view_profile_with_missing_persons(
                    missing_people):
                return False

            profile_for_control_sync = dict(profile)

            if has_active_person and not person:
                profile_for_control_sync.pop('active_person', None)
                has_active_person = False
                try:
                    active_handle = self.get_active()
                except Exception:
                    active_handle = ''

            if has_home_person and not home_person:
                profile_for_control_sync.pop('home_person', None)
                has_home_person = False

        allowed_config_keys = [
            'interface.graphview-ancestor-generations',
            'interface.graphview-descendant-generations',
            'interface.graphview-show-all-connected',
            'interface.graphview-filter-family-tag',
            'interface.graphview-people-limit',
            'interface.graphview-direction',
            'interface.graphview-show-lines',
            'interface.graphview-ranksep',
            'interface.graphview-nodesep',
            'interface.graphview-show-images',
            'interface.graphview-show-id',
            'interface.graphview-show-avatars',
            'interface.graphview-show-full-dates',
            'interface.graphview-show-places',
            'interface.graphview-place-format',
            'interface.graphview-show-tags',
            'interface.graphview-highlight-home-person',
            'interface.graphview-home-path-color',
            'interface.graphview-person-theme',
            'interface.graphview-font',
            'interface.graphview-avatars-style',
            'interface.graphview-person-border-size',
            'interface.graphview-active-person-border-size',
            'interface.graphview-avatars-male',
            'interface.graphview-avatars-female',
            'interface.graphview-avatars-unknown',
            'interface.graphview-avatars-other',
        ]

        loaded_values = {}
        for section_name in ('content', 'layout', 'display', 'style'):
            section = profile.get(section_name, {})
            if isinstance(section, dict):
                loaded_values.update(section)

        self.apply_avatar_profile_load_rules(loaded_values)
        self.apply_profile_people_limit_load_rule(profile, loaded_values)

        # Failure to save the temporary restore point may
        # disable temporary use, but it must never block this View profile or
        # the final graph rebuild.
        self.prepare_temporary_profile_restore_snapshot_before_load()

        if (loaded_values.get('interface.graphview-filter-family-tag') and
                not self.family_tag_filter_value_is_allowed(True)):
            loaded_values['interface.graphview-filter-family-tag'] = False
            if isinstance(profile_for_control_sync, dict):
                profile_for_control_sync = dict(profile_for_control_sync)
                content_data = profile_for_control_sync.get('content')
                if isinstance(content_data, dict):
                    content_data = dict(content_data)
                    content_data[
                        'interface.graphview-filter-family-tag'] = False
                    profile_for_control_sync['content'] = content_data

        self.set_profile_config_values_all_connected_last(
            allowed_config_keys, loaded_values)

        self.temporary_profile_restore_profile_loaded = True
        self.sync_open_config_widgets_after_profile_load()

        if has_home_person and home_person:
            self.dbstate.db.set_default_person_handle(home_handle)

        view_state = profile.get('view_state_optional', {})

        if has_active_person:
            self.change_active(active_handle)

        profile_name = profile.get('profile_name') or os.path.splitext(
            os.path.basename(filename))[0]
        self.set_current_view_profile(filename, profile_name)

        self.clear_standard_profile_controls()
        self.sync_view_profile_controls(profile_for_control_sync)

        if self.graph_widget and active_handle:
            self.graph_widget.populate(active_handle)
            if hasattr(self.graph_widget, 'sync_profile_controls'):
                GLib.idle_add(self.graph_widget.sync_profile_controls)
            if hasattr(self.graph_widget, 'restore_profile_view_state'):
                GLib.timeout_add(
                    200, self.graph_widget.restore_profile_view_state,
                    view_state)

        self.clear_profiles_page_unsaved()
        self.update_profiles_status_labels()
        return True

    def load_graphview_profile(self, _menuitem=None):
        """
        Load a View profile from JSON.
        """
        if not self.profile_function_action_allowed():
            return

        dialog = Gtk.FileChooserDialog(
            title=_('Load View profile'),
            action=Gtk.FileChooserAction.OPEN,
            transient_for=self.uistate.window)
        dialog.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dialog.add_button(_('_Open'), Gtk.ResponseType.OK)

        db_name, media_path, _db_internal_path = self.get_graphview_db_profile_info()
        if media_path and os.path.isdir(media_path):
            dialog.set_current_folder(media_path)
        else:
            mpath = config.get('paths.report-directory')
            if mpath:
                dialog.set_current_folder(os.path.dirname(mpath))

        json_filter = Gtk.FileFilter()
        json_filter.set_name(_('JSON files'))
        json_filter.add_pattern("*.json")
        dialog.add_filter(json_filter)

        response = dialog.run()
        if response != Gtk.ResponseType.OK:
            dialog.destroy()
            return

        filename = dialog.get_filename()
        dialog.destroy()

        self.load_graphview_profile_from_filename(filename, startup_load=False)

    def _get_configure_page_funcs(self):
        """
        Return a list of functions that create gtk elements to use in the
        notebook pages of the Configure dialog.

        :return: list of functions
        """
        return [self.layout_config_panel,
                self.theme_config_panel,
                self.profiles_config_panel,
                self.animation_config_panel,
                self.search_config_panel]

    def layout_config_panel(self, configdialog):
        """
        Function that builds the widget in the configuration dialog.
        See "gramps/gui/configure.py" for details.
        """
        grid = Gtk.Grid()
        grid.set_border_width(12)
        grid.set_column_spacing(6)
        grid.set_row_spacing(6)

        # Remember the ordinary Configure widgets so profile
        # loads can refresh their visible values while this dialog is open.
        self.open_graphview_configdialog = configdialog
        self.open_config_widgets = {}
        self.home_path_color_config_label = None

        row = 0
        widget = configdialog.add_checkbox(
            grid, _('Show images'), row, 'interface.graphview-show-images')
        self.open_config_widgets['interface.graphview-show-images'] = widget
        row += 1
        widget = configdialog.add_checkbox(
            grid, _('Show IDs'), row, 'interface.graphview-show-id')
        self.open_config_widgets['interface.graphview-show-id'] = widget
        row += 1
        widget = configdialog.add_checkbox(
            grid, _('Show avatars'), row, 'interface.graphview-show-avatars')
        self.open_config_widgets['interface.graphview-show-avatars'] = widget
        row += 1
        widget = configdialog.add_checkbox(
            grid, _('Highlight the home person'),
            row, 'interface.graphview-highlight-home-person')
        self.open_config_widgets[
            'interface.graphview-highlight-home-person'] = widget
        row += 1
        widget = configdialog.add_checkbox(
            grid, _('Show full dates'),
            row, 'interface.graphview-show-full-dates')
        self.open_config_widgets[
            'interface.graphview-show-full-dates'] = widget
        row += 1
        widget = configdialog.add_checkbox(
            grid, _('Show places'), row, 'interface.graphview-show-places')
        self.open_config_widgets['interface.graphview-show-places'] = widget
        row += 1
        # Place format:
        p_fmts = [(0, _("Default"))]
        for (indx, fmt) in enumerate(place_displayer.get_formats()):
            p_fmts.append((indx + 1, fmt.name))
        active = self._config.get('interface.graphview-place-format')
        if active >= len(p_fmts):
            active = 1
        widget = configdialog.add_combo(
            grid, _('Place format'), row,
            'interface.graphview-place-format', p_fmts, setactive=active)
        self.open_config_widgets['interface.graphview-place-format'] = widget
        row += 1
        widget = configdialog.add_checkbox(
            grid, _('Show tags'), row, 'interface.graphview-show-tags')
        self.open_config_widgets['interface.graphview-show-tags'] = widget
        row += 1
        direction_fmts = [(0, _("Vertical: Top to Bottom")), (1, _("Vertical: Bottom to Top")), (2, _("Horizontal: Left to Right")), (3, _("Horizontal: Right to Left"))]
        active = self._config.get('interface.graphview-direction')
        widget = configdialog.add_combo(
            grid, _('Time Direction'), row,
            'interface.graphview-direction', direction_fmts, setactive=active)
        self.open_config_widgets['interface.graphview-direction'] = widget
        row += 1
        widget = configdialog.add_checkbox(
            grid, _('Show people with the person tag "ProfileTag"'),
            row, 'interface.graphview-filter-family-tag')
        self.open_config_widgets[
            'interface.graphview-filter-family-tag'] = widget
        row += 1
        people_limit_spinner = configdialog.add_spinner(
            grid, _('Limit number of people displayed (use 0 for unlimited)'),
            row, 'interface.graphview-people-limit', (0, 50_000))
        self.open_config_widgets[
            'interface.graphview-people-limit'] = people_limit_spinner
        self.remember_people_limit_config_spinner(people_limit_spinner)
        if self.people_limit_config_spinner is None:
            self.remember_people_limit_config_spinner(grid)
        self.sync_people_limit_config_spinner()

        return _('Layout'), grid

    def theme_config_panel(self, configdialog):
        """
        Function that builds the widget in the configuration dialog.
        See "gramps/gui/configure.py" for details.
        """
        grid = Gtk.Grid()
        grid.set_border_width(12)
        grid.set_column_spacing(6)
        grid.set_row_spacing(6)

        self.open_graphview_configdialog = configdialog

        p_themes = DotSvgGenerator(self.dbstate, self).get_person_themes()
        themes_list = []
        for t in p_themes:
            themes_list.append((t[0], t[1]))

        row = 0
        widget = configdialog.add_combo(
            grid, _('Person theme'), row,
            'interface.graphview-person-theme', themes_list)
        self.open_config_widgets['interface.graphview-person-theme'] = widget
        row += 1
        color_btn = configdialog.add_color(
            grid, _('Path color to home person'),
            row, 'interface.graphview-home-path-color', col=1)
        self.open_config_widgets[
            'interface.graphview-home-path-color'] = color_btn
        try:
            self.home_path_color_config_label = grid.get_child_at(3, row)
        except Exception:
            self.home_path_color_config_label = None
        row += 1
        font_lbl = Gtk.Label(label=_('Font:'), xalign=0)
        grid.attach(font_lbl, 1, row, 1, 1)
        font = self._config.get('interface.graphview-font')
        font_str = '%s, %d' % (font[0], font[1])
        font_btn = Gtk.FontButton.new_with_font(font_str)
        font_btn.set_show_style(False)
        grid.attach(font_btn, 2, row, 1, 1)
        font_btn.connect('font-set', self.config_change_font)
        font_btn.set_filter_func(self.font_filter_func)
        self.open_config_widgets['interface.graphview-font'] = font_btn

        # Avatars options
        # ===================================================================
        row += 1
        avatars = Avatars(self._config)
        combo = configdialog.add_combo(
            grid, _('Avatars style'), row,
            'interface.graphview-avatars-style', avatars.get_styles_list())
        combo.connect('show', self.cb_on_combo_show)
        self.open_config_widgets['interface.graphview-avatars-style'] = combo

        file_filter = Gtk.FileFilter()
        file_filter.set_name(_('PNG files'))
        file_filter.add_pattern("*.png")

        self.avatar_widgets.clear()
        row += 1
        lbl = Gtk.Label(label=_('Male avatar:'), halign=Gtk.Align.END)
        FCB_male = Gtk.FileChooserButton.new(_('Choose male avatar'),
                                             Gtk.FileChooserAction.OPEN)
        FCB_male.add_filter(file_filter)
        FCB_male.set_filename(
            self._config.get('interface.graphview-avatars-male'))
        FCB_male.connect('file-set', self.cb_male_avatar_set)
        grid.attach(lbl, 1, row, 1, 1)
        grid.attach(FCB_male, 2, row, 1, 1)
        self.avatar_widgets.append(lbl)
        self.avatar_widgets.append(FCB_male)
        self.open_config_widgets[
            'interface.graphview-avatars-male'] = FCB_male

        row += 1
        lbl = Gtk.Label(label=_('Female avatar:'), halign=Gtk.Align.END)
        FCB_female = Gtk.FileChooserButton.new(_('Choose female avatar'),
                                               Gtk.FileChooserAction.OPEN)
        FCB_female.connect('file-set', self.cb_female_avatar_set)
        FCB_female.add_filter(file_filter)
        FCB_female.set_filename(
            self._config.get('interface.graphview-avatars-female'))
        grid.attach(lbl, 1, row, 1, 1)
        grid.attach(FCB_female, 2, row, 1, 1)
        self.avatar_widgets.append(lbl)
        self.avatar_widgets.append(FCB_female)
        self.open_config_widgets[
            'interface.graphview-avatars-female'] = FCB_female

        row += 1
        lbl = Gtk.Label(label=_('Unknown avatar:'), halign=Gtk.Align.END)
        FCB_unknown = Gtk.FileChooserButton.new(_('Choose Unknown avatar'),
                                             Gtk.FileChooserAction.OPEN)
        FCB_unknown.add_filter(file_filter)
        FCB_unknown.set_filename(
            self._config.get('interface.graphview-avatars-unknown'))
        FCB_unknown.connect('file-set', self.cb_unknown_avatar_set)
        grid.attach(lbl, 1, row, 1, 1)
        grid.attach(FCB_unknown, 2, row, 1, 1)
        self.avatar_widgets.append(lbl)
        self.avatar_widgets.append(FCB_unknown)
        self.open_config_widgets[
            'interface.graphview-avatars-unknown'] = FCB_unknown

        row += 1
        lbl = Gtk.Label(label=_('Other avatar:'), halign=Gtk.Align.END)
        FCB_other = Gtk.FileChooserButton.new(_('Choose Other avatar'),
                                             Gtk.FileChooserAction.OPEN)
        FCB_other.add_filter(file_filter)
        FCB_other.set_filename(
            self._config.get('interface.graphview-avatars-other'))
        FCB_other.connect('file-set', self.cb_other_avatar_set)
        grid.attach(lbl, 1, row, 1, 1)
        grid.attach(FCB_other, 2, row, 1, 1)
        self.avatar_widgets.append(lbl)
        self.avatar_widgets.append(FCB_other)
        self.open_config_widgets[
            'interface.graphview-avatars-other'] = FCB_other
        # ===================================================================

        row += 1
        widget = configdialog.add_spinner(
            grid, _('Active person border size'),
            row, 'interface.graphview-active-person-border-size', (1, 20))
        self.open_config_widgets[
            'interface.graphview-active-person-border-size'] = widget

        row += 1
        widget = configdialog.add_spinner(
            grid, _('Person border size'),
            row, 'interface.graphview-person-border-size', (1, 20))
        self.open_config_widgets[
            'interface.graphview-person-border-size'] = widget

        return _('Themes'), grid

    def cb_profile_standard_bool_toggled(self, checkbutton, config_key):
        """
        Let selected boolean Standard-profile boxes in
        the Profiles tab update Graph View immediately, like the normal
        configuration tabs do. The same state is also remembered as a
        Standard-profile save choice.

        Selected boolean Standard-profile boxes are saved as normal
        true/false values when Save standard profile is pressed.
        """
        if getattr(self, 'updating_standard_profile_controls', False):
            return

        if not self.profile_function_action_allowed():
            return

        value = checkbutton.get_active()
        if (config_key == 'interface.graphview-filter-family-tag' and
                value and
                not self.family_tag_filter_value_is_allowed(True)):
            self.updating_standard_profile_controls = True
            try:
                checkbutton.set_active(False)
            finally:
                self.updating_standard_profile_controls = False
            value = False

        if not hasattr(self, 'standard_profile_save_choices'):
            self.standard_profile_save_choices = {}
        self.standard_profile_save_choices[config_key] = value

        self._config.set(config_key, value)

        if config_key == 'interface.graphview-show-id':
            self.show_ID = value
        elif config_key == 'interface.graphview-show-images':
            self.show_images = value
        elif config_key == 'interface.graphview-show-avatars':
            self.show_avatars = value
        elif config_key == 'interface.graphview-highlight-home-person':
            self.highlight_home_person = value
        elif config_key == 'interface.graphview-show-full-dates':
            self.show_full_dates = value
        elif config_key == 'interface.graphview-show-places':
            self.show_places = value
        elif config_key == 'interface.graphview-show-tags':
            self.show_tag_color = value
        elif config_key == 'interface.graphview-show-all-connected':
            if self.graph_widget and hasattr(self.graph_widget, 'all_connected_btn'):
                if self.graph_widget.all_connected_btn.get_active() != value:
                    self.graph_widget.all_connected_btn.set_active(value)

        self.update_profile_avatar_controls_sensitivity()
        self.mark_profiles_page_unsaved()

        if self.graph_widget and self.get_active():
            self.graph_widget.populate(self.get_active())

    def cb_profile_standard_save_only_bool_toggled(self, checkbutton, config_key):
        """
        Remember Standard-profile boolean values that should
        be saved, but do not update/redraw Graph View immediately.
        """
        if getattr(self, 'updating_standard_profile_controls', False):
            return

        if not self.profile_function_action_allowed():
            return

        if not hasattr(self, 'standard_profile_save_choices'):
            self.standard_profile_save_choices = {}
        self.standard_profile_save_choices[config_key] = checkbutton.get_active()
        self.mark_profiles_page_unsaved()

    def cb_profile_standard_group_toggled(self, checkbutton, group_name):
        """
        Remember whether a Standard-profile group should be
        saved and restored. These group checkboxes do not change Graph View
        immediately; they only decide whether the related values are present
        in the standard profile JSON and therefore loaded later.
        """
        if getattr(self, 'updating_standard_profile_controls', False):
            return

        if not self.profile_function_action_allowed():
            return

        if not hasattr(self, 'standard_profile_group_choices'):
            self.standard_profile_group_choices = {}
        self.standard_profile_group_choices[group_name] = checkbutton.get_active()
        self.mark_profiles_page_unsaved()

    def sync_standard_profile_controls(self):
        """
        Update the Standard-profile checkboxes while the Configure dialog is
        open. This is used after Load standard profile so the Profiles page
        reflects the values that are now active without closing/reopening the
        dialog.
        """
        checkbox_info = getattr(self, 'profile_standard_checkbox_info', [])
        if not checkbox_info:
            return False

        if not hasattr(self, 'standard_profile_save_choices'):
            self.standard_profile_save_choices = {}
        if not hasattr(self, 'standard_profile_group_choices'):
            self.standard_profile_group_choices = {}

        standard_profile_exists = bool(
            self.standard_profile_controls_active and
            self.standard_graphview_profile_exists())
        standard_profile_data = {}
        if standard_profile_exists:
            standard_profile_data = self.read_standard_profile_for_choices()
            if not standard_profile_data:
                standard_profile_exists = False

        self.updating_standard_profile_controls = True
        try:
            for info in checkbox_info:
                checkbutton = info.get('checkbutton')
                if checkbutton is None:
                    continue

                standard_default = info.get('standard_default', True)
                live_config_key = info.get('live_config_key')
                save_only_config_key = info.get('save_only_config_key')

                if not standard_profile_exists:
                    checkbutton.set_active(False)
                    if live_config_key:
                        self.standard_profile_save_choices[live_config_key] = False
                    elif save_only_config_key:
                        if save_only_config_key.startswith('group:'):
                            group_name = save_only_config_key.split(':', 1)[1]
                            self.standard_profile_group_choices[group_name] = False
                        else:
                            self.standard_profile_save_choices[save_only_config_key] = False
                    continue

                if live_config_key:
                    value = self.get_standard_profile_choice_value(
                        standard_profile_data, live_config_key, False)
                    checkbutton.set_active(bool(value))
                    self.standard_profile_save_choices[live_config_key] = (
                        checkbutton.get_active())
                elif save_only_config_key:
                    if save_only_config_key.startswith('group:'):
                        group_name = save_only_config_key.split(':', 1)[1]
                        value = self.standard_profile_group_is_enabled(
                            group_name, standard_default)
                        checkbutton.set_active(bool(value))
                        self.standard_profile_group_choices[group_name] = (
                            checkbutton.get_active())
                    else:
                        value = self.get_standard_profile_choice_value(
                            standard_profile_data, save_only_config_key, False)
                        checkbutton.set_active(bool(value))
                        self.standard_profile_save_choices[save_only_config_key] = (
                            checkbutton.get_active())
                else:
                    checkbutton.set_active(bool(standard_default))
        finally:
            self.updating_standard_profile_controls = False

        self.update_profile_avatar_controls_sensitivity()
        self.update_profile_people_limit_controls_sensitivity()
        return False

    def clear_standard_profile_controls(self):
        """
        Clear the Standard-profile column after the Standard profile is deleted.

        This is only a profile-page reset. It must not change current
        Graph View settings or redraw the graph.
        """
        self.standard_profile_controls_active = False

        if not hasattr(self, 'standard_profile_save_choices'):
            self.standard_profile_save_choices = {}
        if not hasattr(self, 'standard_profile_group_choices'):
            self.standard_profile_group_choices = {}

        self.updating_standard_profile_controls = True
        try:
            for info in getattr(self, 'profile_standard_checkbox_info', []):
                checkbutton = info.get('checkbutton')
                if checkbutton is None:
                    continue

                live_config_key = info.get('live_config_key')
                save_only_config_key = info.get('save_only_config_key')

                checkbutton.set_active(False)

                if live_config_key:
                    self.standard_profile_save_choices[live_config_key] = False
                elif save_only_config_key:
                    if save_only_config_key.startswith('group:'):
                        group_name = save_only_config_key.split(':', 1)[1]
                        self.standard_profile_group_choices[group_name] = False
                    else:
                        self.standard_profile_save_choices[save_only_config_key] = False
        finally:
            self.updating_standard_profile_controls = False

        self.update_profile_function_controls_sensitivity()
        return False

    def get_standard_profile_section_for_choices(self, section_name):
        """
        Read the current Standard-profile section so Profiles-tab group
        checkboxes can reflect what will actually be restored.

        If the Standard profile has been deleted, the
        Standard column remains clean.
        """
        try:
            self.clean_first_standard_profile_if_created_from_backup()
            filename = self.get_standard_profile_filename()
            if not os.path.isfile(filename):
                return {}
            with open(filename, 'r', encoding='utf-8') as json_file:
                profile = json.load(json_file)
            section = profile.get(section_name, {})
            if isinstance(section, dict):
                return section
        except Exception:
            pass
        return {}

    def profiles_config_panel(self, configdialog):
        """
        Function that builds the Profiles page in the configuration dialog.

        Keep the stable Standard/View profile logic. The selected boolean
        Standard-profile and View-profile boxes update Graph View immediately.
        Load-only choices are marked with a small footnote in the Profiles
        page.
        """
        self.profile_function_controls = []

        outer = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
        outer.set_border_width(12)

        # The standard Gramps Configure dialog has a generic
        # tooltip saying "Any changes are saved immediately". That is
        # misleading on the Profiles page because some boxes update live,
        # while the ¹ choices only decide what is saved/restored later.
        # Remove the generic tooltip only while the Profiles page is active,
        # and restore it again on the other Graph View Configure pages.
        try:
            original_window_tooltip = configdialog.window.get_tooltip_text()
        except Exception:
            original_window_tooltip = None

        def update_window_tooltip_for_profiles_tab():
            try:
                profile_page_number = configdialog.panel.page_num(outer)
                if (profile_page_number >= 0 and
                        configdialog.panel.get_current_page() ==
                        profile_page_number):
                    configdialog.window.set_tooltip_text(None)
                else:
                    configdialog.window.set_tooltip_text(
                        original_window_tooltip)
            except Exception:
                pass
            return False

        def on_profiles_tab_switch(_notebook, _page, _page_num):
            GLib.idle_add(update_window_tooltip_for_profiles_tab)

        try:
            configdialog.panel.connect('switch-page', on_profiles_tab_switch)
            GLib.idle_add(update_window_tooltip_for_profiles_tab)
        except Exception:
            pass

        # Keep the complete, proven close protection.
        # delete-event guards the window X; response guards normal GTK close;
        # the direct button handlers detect Gramps' special Close button.
        # After "Close anyway", request_profiles_configure_close() performs
        # the actual close through Gtk.ResponseType.CLOSE.
        try:
            if self.profiles_config_window is not configdialog.window:
                self.profiles_config_window = configdialog.window
                self.profiles_config_close_button_ids = set()
                self.profiles_config_force_close_once = False
                self.profiles_config_delete_handler_id = (
                    configdialog.window.connect(
                        'delete-event',
                        self.cb_profiles_configure_delete_event))
                try:
                    self.profiles_config_response_handler_id = (
                        configdialog.window.connect(
                            'response',
                            self.cb_profiles_configure_response))
                except Exception:
                    self.profiles_config_response_handler_id = None
            GLib.idle_add(
                self.install_profiles_close_button_guard,
                configdialog.window)
        except Exception:
            pass

        # The profile function is opt-in. When enabled for
        # the first time, a complete original-settings backup is created.
        # No Standard profile is created automatically.
        # Compact Profiles layout for smaller screens.
        # The two master options share the top row, while startup choices
        # stay on one line underneath.
        startup_grid = Gtk.Grid()
        startup_grid.set_column_spacing(12)
        startup_grid.set_row_spacing(2)
        startup_grid.set_column_homogeneous(True)
        startup_grid.set_margin_top(2)
        startup_grid.set_margin_bottom(2)
        outer.pack_start(startup_grid, False, False, 0)

        profile_feature_check = Gtk.CheckButton(
            label=_('Enable profile function'))
        profile_feature_check.set_tooltip_text(
            _('When enabled, Graph View profiles can be used, and a selected '
              'profile can be loaded at startup.'))
        profile_feature_check.set_active(self.profile_function_is_enabled())
        profile_feature_check.connect(
            'toggled', self.cb_profile_feature_enable_toggled)
        self.profile_feature_enable_checkbox = profile_feature_check
        startup_grid.attach(profile_feature_check, 0, 0, 2, 1)

        backup_info = Gtk.Label(
            label=_(
                'When enabled for the first time, the current Graph View '
                'settings are saved as the original settings backup. This '
                'backup is never overwritten.'),
            xalign=0)
        backup_info.set_line_wrap(True)
        backup_info.set_margin_start(22)
        # Keep both help texts aligned at the top when
        # the left text wraps onto an extra line on a smaller screen.
        backup_info.set_valign(Gtk.Align.START)
        backup_info.set_yalign(0.0)
        startup_grid.attach(backup_info, 0, 1, 2, 1)

        temporary_check = Gtk.CheckButton(
            label=_('Use profiles temporarily'))
        temporary_check.set_tooltip_text(
            _('Restore the Graph View settings that were active when the '
              'family tree was opened.'))
        temporary_check.set_active(self.profiles_temporary_is_enabled())
        temporary_check.connect(
            'toggled', self.cb_profiles_temporary_toggled)
        self.profile_temporary_checkbox = temporary_check
        self.register_profile_function_control(temporary_check)
        startup_grid.attach(temporary_check, 2, 0, 2, 1)

        temporary_info = Gtk.Label(
            label=_(
                'Restore the Graph View settings that were active when the '
                'family tree was opened.'),
            xalign=0)
        temporary_info.set_line_wrap(True)
        temporary_info.set_margin_start(22)
        temporary_info.set_valign(Gtk.Align.START)
        temporary_info.set_yalign(0.0)
        self.register_profile_function_control(temporary_info)
        startup_grid.attach(temporary_info, 2, 1, 2, 1)

        startup_label = Gtk.Label(label=_('Apply at startup:'), xalign=0)
        startup_label.set_margin_top(4)
        startup_label.set_margin_start(28)
        startup_grid.attach(startup_label, 0, 2, 1, 1)

        startup_radio_box = Gtk.Box(
            orientation=Gtk.Orientation.HORIZONTAL, spacing=28)
        startup_radio_box.set_margin_top(4)
        startup_grid.attach(startup_radio_box, 1, 2, 3, 1)

        startup_none_radio = Gtk.RadioButton.new_with_label_from_widget(
            None, _('No profile'))
        startup_none_radio.connect(
            'toggled', self.cb_profile_startup_mode_toggled, 'none')
        self.profile_startup_none_radio = startup_none_radio
        self.register_profile_function_control(startup_none_radio)
        startup_radio_box.pack_start(startup_none_radio, False, False, 0)

        startup_standard_radio = Gtk.RadioButton.new_with_label_from_widget(
            startup_none_radio, _('Standard profile'))
        startup_standard_radio.connect(
            'toggled', self.cb_profile_startup_mode_toggled, 'standard')
        self.profile_startup_standard_radio = startup_standard_radio
        self.register_profile_function_control(startup_standard_radio)
        startup_radio_box.pack_start(startup_standard_radio, False, False, 0)

        startup_view_radio = Gtk.RadioButton.new_with_label_from_widget(
            startup_none_radio, _('Current View profile'))
        startup_view_radio.connect(
            'toggled', self.cb_profile_startup_mode_toggled, 'view')
        self.profile_startup_view_radio = startup_view_radio
        self.register_profile_function_control(startup_view_radio)
        startup_radio_box.pack_start(startup_view_radio, False, False, 0)
        self.sync_profile_startup_controls()

        # Beginner-friendly full snapshot actions. These buttons
        # read the current Graph View directly and do not depend on the
        # individual choices below.
        quick_save_box = Gtk.Box(
            orientation=Gtk.Orientation.VERTICAL, spacing=2)
        quick_save_box.set_margin_top(4)
        quick_save_box.set_margin_start(32)
        outer.pack_start(quick_save_box, False, False, 0)

        quick_save_title = Gtk.Label(label=_('Save current view:'), xalign=0)
        quick_save_title.set_markup(
            '<b>%s</b>' % escape(_('Save current view:')))
        self.register_profile_function_control(quick_save_title)
        quick_save_box.pack_start(quick_save_title, False, False, 0)

        quick_save_info = Gtk.Label(
            label=_(
                'Save all supported settings from the current Graph View '
                'without changing the graph.'),
            xalign=0)
        quick_save_info.set_line_wrap(True)
        self.register_profile_function_control(quick_save_info)
        quick_save_box.pack_start(quick_save_info, False, False, 0)

        quick_save_buttons = Gtk.Box(
            orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        quick_save_buttons.set_halign(Gtk.Align.CENTER)
        quick_save_buttons.set_margin_top(2)
        quick_save_box.pack_start(quick_save_buttons, False, False, 0)

        quick_standard_btn = Gtk.Button(
            label=_('Save as Standard profile'))
        quick_standard_btn.set_tooltip_text(
            _('Save all supported current settings to the Standard profile.'))
        quick_standard_btn.connect(
            'clicked', self.save_current_view_as_standard_profile)
        self.register_profile_function_control(quick_standard_btn)
        quick_save_buttons.pack_start(
            quick_standard_btn, False, False, 0)

        quick_view_btn = Gtk.Button(
            label=_('Save as new View profile...'))
        quick_view_btn.set_tooltip_text(
            _('Save the complete current view to a new View profile file.'))
        quick_view_btn.connect(
            'clicked', self.save_current_view_as_new_view_profile)
        self.register_profile_function_control(quick_view_btn)
        quick_save_buttons.pack_start(quick_view_btn, False, False, 0)

        custom_title = Gtk.Label(
            label=_('Or choose settings to include'), xalign=0)
        custom_title.set_markup(
            '<b>%s</b>' % escape(_('Or choose settings to include')))
        custom_title.set_margin_top(6)
        custom_title.set_margin_start(32)
        self.register_profile_function_control(custom_title)
        outer.pack_start(custom_title, False, False, 0)

        # A responsive separator between the section heading
        # and its explanatory text. The equal margins align it with the
        # surrounding text, while hexpand makes it follow the window width.
        custom_separator = Gtk.Separator(
            orientation=Gtk.Orientation.HORIZONTAL)
        custom_separator.set_margin_start(32)
        custom_separator.set_margin_end(32)
        custom_separator.set_margin_top(3)
        custom_separator.set_margin_bottom(3)
        custom_separator.set_hexpand(True)
        self.register_profile_function_control(custom_separator)
        outer.pack_start(custom_separator, False, True, 0)

        custom_info = Gtk.Label(
            label=_(
                'Select individual settings for a customised Standard or '
                'View profile.'),
            xalign=0)
        custom_info.set_line_wrap(True)
        custom_info.set_margin_start(32)
        custom_info.set_margin_end(32)
        self.register_profile_function_control(custom_info)
        outer.pack_start(custom_info, False, False, 0)

        scrolled = Gtk.ScrolledWindow()
        scrolled.set_policy(Gtk.PolicyType.NEVER, Gtk.PolicyType.AUTOMATIC)
        scrolled.set_shadow_type(Gtk.ShadowType.NONE)
        scrolled.set_margin_start(32)
        outer.pack_start(scrolled, True, True, 0)

        grid = Gtk.Grid()
        grid.set_column_spacing(12)
        grid.set_row_spacing(4)
        grid.set_border_width(2)
        scrolled.add(grid)

        title_label = Gtk.Label(label=_('Profile content'), xalign=0)
        title_label.set_markup('<b>%s</b>' % escape(_('Profile content')))
        grid.attach(title_label, 0, 0, 1, 1)

        standard_label = Gtk.Label(label=_('Standard profile'), xalign=0.5)
        standard_label.set_markup('<b>%s</b>' % escape(_('Standard profile')))
        grid.attach(standard_label, 1, 0, 1, 1)

        view_label = Gtk.Label(label=_('View profile'), xalign=0.5)
        view_label.set_markup('<b>%s</b>' % escape(_('View profile')))
        grid.attach(view_label, 2, 0, 1, 1)

        # (label, standard default, view default, standard live config key,
        #  standard save-only boolean config key, view save-choice key,
        #  view live boolean config key)
        # Use None for standard default when Standard profile must not offer
        # that choice. Media path is intentionally not shown as a user choice.
        # Selected boolean options update Graph View live and are saved as
        # normal true/false values. Show people with the person tag "ProfileTag"
        # updates live in both profile columns. All ¹ rows are load-only
        # include/exclude choices: selected saves their value(s), unselected
        # removes their JSON line(s). Limit number displayed is the exception:
        # its value is always stored, while the positive-limit choice is stored
        # separately. All connected is true/false and updates live.
        # Show places includes Place format.
        # Keep Home and Active person first because they are View-profile
        # person choices rather than ordinary Graph View settings. The
        # remaining rows follow their English display names alphabetically,
        # except Show images stays immediately before the dependent
        # Show avatars & style option.
        profile_rows = [
            (_('Home person¹'), None, True, None, None, 'home_person', None),
            (_('Active person¹'), None, True, None, None, 'active_person', None),
            (_('Active person border size¹'), True, True, None, 'group:active_person_border_size', 'active_person_border_size', None),
            (_('All connected'), False, True, 'interface.graphview-show-all-connected', None, None, 'interface.graphview-show-all-connected'),
            (_('Font¹'), True, True, None, 'group:font', 'font', None),
            (_('Generations¹'), False, True, None, 'group:generations', 'generations', None),
            (_('Highlight the home person'), True, True, 'interface.graphview-highlight-home-person', None, None, 'interface.graphview-highlight-home-person'),
            (_('Limit number of people displayed¹'), False, True, None, 'group:people_limit', 'people_limit', None),
            (_('Lines type¹'), True, True, None, 'group:line_types', 'line_types', None),
            (_('Path color to home person¹'), True, True, None, 'group:path_color', 'path_color', None),
            (_('Person border size¹'), True, True, None, 'group:person_border_size', 'person_border_size', None),
            (_('Show full dates'), True, True, 'interface.graphview-show-full-dates', None, None, 'interface.graphview-show-full-dates'),
            (_('Show IDs'), True, True, 'interface.graphview-show-id', None, None, 'interface.graphview-show-id'),
            (_('Show images'), True, True, 'interface.graphview-show-images', None, None, 'interface.graphview-show-images'),
            (_('Show avatars & style'), True, True, 'interface.graphview-show-avatars', None, None, 'interface.graphview-show-avatars'),
            (_('Show people with the person tag "ProfileTag"'), False, True, 'interface.graphview-filter-family-tag', None, None, 'interface.graphview-filter-family-tag'),
            (_('Show places & format'), True, True, 'interface.graphview-show-places', None, None, 'interface.graphview-show-places'),
            (_('Show tags'), True, True, 'interface.graphview-show-tags', None, None, 'interface.graphview-show-tags'),
            (_('Spacings¹'), True, True, None, 'group:spacings', 'spacings', None),
            (_('Theme¹'), True, True, None, 'group:theme', 'theme', None),
            (_('Time direction¹'), True, True, None, 'group:time_direction', 'time_direction', None),
            (_('Zoom & chart position¹'), False, True, None, 'group:view_state', 'view_state', None),
        ]

        self.profile_standard_checkbuttons = []
        self.profile_standard_checkbox_info = []
        self.profile_view_checkbuttons = []
        self.profile_view_checkbox_info = []
        self.profile_standard_show_images_checkbox = None
        self.profile_standard_show_avatars_checkbox = None
        self.profile_view_show_images_checkbox = None
        self.profile_view_show_avatars_checkbox = None
        self.view_profile_save_choices = getattr(
            self, 'view_profile_save_choices',
            self.get_empty_view_profile_save_choices())
        if not self.current_view_profile_filename:
            self.view_profile_save_choices = self.get_empty_view_profile_save_choices()
        self.standard_profile_save_choices = getattr(
            self, 'standard_profile_save_choices', {})
        self.standard_profile_group_choices = getattr(
            self, 'standard_profile_group_choices', {})
        standard_profile_exists_for_controls = bool(
            self.standard_profile_controls_active and
            self.standard_graphview_profile_exists())
        standard_profile_data_for_controls = {}
        if standard_profile_exists_for_controls:
            standard_profile_data_for_controls = (
                self.read_standard_profile_for_choices())
            if not standard_profile_data_for_controls:
                standard_profile_exists_for_controls = False
        row = 1
        for (label_text, standard_default, view_default, live_config_key,
             save_only_config_key, view_choice_key,
             view_config_key) in profile_rows:
            label = Gtk.Label(label=label_text, xalign=0)
            grid.attach(label, 0, row, 1, 1)

            if standard_default is None:
                standard_placeholder = Gtk.Label(label='')
                grid.attach(standard_placeholder, 1, row, 1, 1)
            else:
                standard_check = Gtk.CheckButton()
                standard_check.set_halign(Gtk.Align.CENTER)
                if not standard_profile_exists_for_controls:
                    standard_check.set_active(False)
                    if live_config_key:
                        self.standard_profile_save_choices[live_config_key] = False
                        standard_check.connect(
                            'toggled',
                            self.cb_profile_standard_bool_toggled,
                            live_config_key)
                    elif save_only_config_key:
                        if save_only_config_key.startswith('group:'):
                            group_name = save_only_config_key.split(':', 1)[1]
                            self.standard_profile_group_choices[group_name] = False
                            standard_check.connect(
                                'toggled',
                                self.cb_profile_standard_group_toggled,
                                group_name)
                        else:
                            self.standard_profile_save_choices[save_only_config_key] = False
                            standard_check.connect(
                                'toggled',
                                self.cb_profile_standard_save_only_bool_toggled,
                                save_only_config_key)
                elif live_config_key:
                    standard_check.set_active(bool(
                        self.get_standard_profile_choice_value(
                            standard_profile_data_for_controls,
                            live_config_key, False)))
                    self.standard_profile_save_choices[live_config_key] = (
                        standard_check.get_active())
                    standard_check.connect(
                        'toggled',
                        self.cb_profile_standard_bool_toggled,
                        live_config_key)
                elif save_only_config_key:
                    if save_only_config_key.startswith('group:'):
                        group_name = save_only_config_key.split(':', 1)[1]
                        group_active = self.standard_profile_group_is_enabled(
                            group_name, standard_default)
                        standard_check.set_active(group_active)
                        self.standard_profile_group_choices[group_name] = (
                            standard_check.get_active())
                        standard_check.connect(
                            'toggled',
                            self.cb_profile_standard_group_toggled,
                            group_name)
                    else:
                        standard_check.set_active(bool(
                            self.get_standard_profile_choice_value(
                                standard_profile_data_for_controls,
                                save_only_config_key, False)))
                        self.standard_profile_save_choices[save_only_config_key] = (
                            standard_check.get_active())
                        standard_check.connect(
                            'toggled',
                            self.cb_profile_standard_save_only_bool_toggled,
                            save_only_config_key)
                else:
                    standard_check.set_active(standard_default)
                self.register_profile_function_control(standard_check)
                grid.attach(standard_check, 1, row, 1, 1)
                self.profile_standard_checkbuttons.append(standard_check)
                self.profile_standard_checkbox_info.append({
                    'checkbutton': standard_check,
                    'standard_default': standard_default,
                    'live_config_key': live_config_key,
                    'save_only_config_key': save_only_config_key,
                })
                if live_config_key == 'interface.graphview-show-images':
                    self.profile_standard_show_images_checkbox = standard_check
                elif live_config_key == 'interface.graphview-show-avatars':
                    self.profile_standard_show_avatars_checkbox = standard_check
                elif save_only_config_key == 'group:people_limit':
                    self.profile_standard_people_limit_checkbox = standard_check

            view_check = Gtk.CheckButton()
            view_check.set_halign(Gtk.Align.CENTER)
            if view_config_key:
                view_check.set_active(bool(
                    self.view_profile_save_choices.get(
                        view_config_key, False)))
                view_check.connect(
                    'toggled', self.cb_profile_view_bool_toggled,
                    view_config_key)
            elif view_choice_key:
                view_check.set_active(bool(
                    self.view_profile_save_choices.get(
                        view_choice_key, view_default)))
                view_check.connect(
                    'toggled', self.cb_profile_view_choice_toggled,
                    view_choice_key)
            else:
                view_check.set_active(view_default)
            self.register_profile_function_control(view_check)
            grid.attach(view_check, 2, row, 1, 1)
            self.profile_view_checkbuttons.append(view_check)
            self.profile_view_checkbox_info.append({
                'checkbutton': view_check,
                'choice_key': view_choice_key,
                'view_config_key': view_config_key,
                'default_value': view_default,
            })
            if view_config_key == 'interface.graphview-show-images':
                self.profile_view_show_images_checkbox = view_check
            elif view_config_key == 'interface.graphview-show-avatars':
                self.profile_view_show_avatars_checkbox = view_check
            elif view_choice_key == 'people_limit':
                self.profile_view_people_limit_checkbox = view_check

            row += 1

        self.update_profile_avatar_controls_sensitivity()
        self.update_profile_people_limit_controls_sensitivity()

        note = Gtk.Label(
            label=_('¹ saved in profiles; applied on load only.'),
            xalign=0)
        note.set_line_wrap(True)
        note.set_margin_start(32)
        outer.pack_start(note, False, False, 0)

                # Compact status line. Current View and Standard
        # status share one row, with Standard status aligned to the right.
        status_line = Gtk.Box(
            orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        status_line.set_margin_start(32)
        status_line.set_margin_end(32)
        outer.pack_start(status_line, False, False, 4)

        status_title = Gtk.Label(label=_('Status:'), xalign=0)
        status_title.set_markup('<b>%s</b>' % escape(_('Status:')))
        status_line.pack_start(status_title, False, False, 0)

        current_text = _('Current View profile: none')
        if self.current_view_profile_name:
            current_text = (_('Current View profile: %s') %
                            self.current_view_profile_name)
        self.current_view_profile_status_label = Gtk.Label(
            label=current_text, xalign=0)
        status_line.pack_start(
            self.current_view_profile_status_label, False, False, 0)

        status_spacer = Gtk.Box()
        status_line.pack_start(status_spacer, True, True, 0)

        standard_text = _('Standard profile: not saved')
        if self.standard_graphview_profile_exists():
            standard_text = _('Standard profile: saved')
        self.standard_profile_status_label = Gtk.Label(
            label=standard_text, xalign=1)
        status_line.pack_end(
            self.standard_profile_status_label, False, False, 0)

        status_grid = Gtk.Grid()
        status_grid.set_column_spacing(8)
        status_grid.set_row_spacing(5)
        status_grid.set_margin_start(32)
        status_grid.set_margin_end(32)
        outer.pack_start(status_grid, False, False, 0)

        view_buttons_label = Gtk.Label(label=_('View profile:'), xalign=0)
        status_grid.attach(view_buttons_label, 0, 0, 4, 1)

        save_current_btn = Gtk.Button(label=_('Save current View profile'))
        save_current_btn.set_tooltip_text(
            _('Save changes to the current View profile.'))
        save_current_btn.connect('clicked', self.save_current_view_profile)
        self.register_profile_function_control(save_current_btn)
        save_current_btn.set_sensitive(
            bool(self.current_view_profile_filename))
        self.current_view_profile_save_button = save_current_btn
        status_grid.attach(save_current_btn, 0, 1, 1, 1)

        save_as_btn = Gtk.Button(label=_('Save as...'))
        self.register_profile_function_control(save_as_btn)
        save_as_btn.connect(
            'clicked',
            lambda button: self.save_graphview_profile(
                button, 'view_profile'))
        status_grid.attach(save_as_btn, 1, 1, 1, 1)

        load_btn = Gtk.Button(label=_('Load...'))
        self.register_profile_function_control(load_btn)
        load_btn.connect('clicked', self.load_graphview_profile)
        status_grid.attach(load_btn, 2, 1, 1, 1)

        delete_view_btn = Gtk.Button(label=_('Delete'))
        self.register_profile_function_control(delete_view_btn)
        delete_view_btn.connect('clicked', self.delete_current_view_profile)
        delete_view_btn.set_sensitive(
            bool(self.current_view_profile_filename))
        self.current_view_profile_delete_button = delete_view_btn
        status_grid.attach(delete_view_btn, 3, 1, 1, 1)

        standard_buttons_label = Gtk.Label(
            label=_('Standard profile:'), xalign=0)
        standard_buttons_label.set_margin_top(8)
        status_grid.attach(standard_buttons_label, 0, 2, 4, 1)

        save_standard_btn = Gtk.Button(label=_('Save standard profile'))
        self.register_profile_function_control(save_standard_btn)
        save_standard_btn.connect(
            'clicked', self.save_selected_standard_profile)
        status_grid.attach(save_standard_btn, 0, 3, 1, 1)

        load_standard_btn = Gtk.Button(label=_('Load standard profile'))
        self.register_profile_function_control(load_standard_btn)
        load_standard_btn.connect(
            'clicked', self.load_standard_graphview_profile)
        load_standard_btn.set_sensitive(
            self.profile_function_is_enabled() and
            self.standard_graphview_profile_exists())
        self.standard_profile_load_button = load_standard_btn
        status_grid.attach(load_standard_btn, 1, 3, 1, 1)

        delete_standard_btn = Gtk.Button(label=_('Delete'))
        self.register_profile_function_control(delete_standard_btn)
        delete_standard_btn.connect(
            'clicked', self.delete_standard_graphview_profile)
        delete_standard_btn.set_sensitive(
            self.standard_graphview_profile_exists())
        self.standard_profile_delete_button = delete_standard_btn
        status_grid.attach(delete_standard_btn, 3, 3, 1, 1)

        self.update_profiles_status_labels()

        return _('Profiles'), outer

    def animation_config_panel(self, configdialog):
        """
        Function that builds the widget in the configuration dialog.
        See "gramps/gui/configure.py" for details.
        """
        grid = Gtk.Grid()
        grid.set_border_width(12)
        grid.set_column_spacing(6)
        grid.set_row_spacing(6)

        configdialog.add_checkbox(
            grid, _('Show animation'),
            0, 'interface.graphview-show-animation')
        self.ani_widgets.clear()
        widget = configdialog.add_spinner(
            grid, _('Animation speed (1..5 and 5 is the slower)'),
            1, 'interface.graphview-animation-speed', (1, 5))
        self.ani_widgets.append(widget)
        widget = configdialog.add_spinner(
            grid, _('Animation count (0..8 use 0 to turn off)'),
            2, 'interface.graphview-animation-count', (0, 8))
        self.ani_widgets.append(widget)

        # disable animate options if needed
        if not self.graph_widget.animation.show_animation:
            for widget in self.ani_widgets:
                widget.set_sensitive(False)

        return _('Animation'), grid

    def search_config_panel(self, configdialog):
        """
        Function that builds the widget in the configuration dialog.
        See "gramps/gui/configure.py" for details.
        """
        grid = Gtk.Grid()
        grid.set_border_width(12)
        grid.set_column_spacing(6)
        grid.set_row_spacing(6)

        row = 0
        widget = configdialog.add_checkbox(
            grid, _('Search in all database'), row,
            'interface.graphview-search-all-db')
        widget.set_tooltip_text(_("Also apply search by all database."))
        row += 1
        widget = configdialog.add_checkbox(
            grid, _('Show person images'), row,
            'interface.graphview-search-show-images')
        widget.set_tooltip_text(
            _("Show persons thumbnails in search result list."))
        row += 1
        widget = configdialog.add_checkbox(
            grid, _('Show bookmarked first'), row,
            'interface.graphview-search-marked-first')
        widget.set_tooltip_text(
            _("Show bookmarked persons first in search result list."))

        return _('Search'), grid

    def font_filter_func(self, _family, face):
        """
        Filter function to display only regular fonts.
        """
        desc = face.describe()
        stretch = desc.get_stretch()
        if stretch != Pango.Stretch.NORMAL:
            return False  # avoid Condensed or Expanded
        sty = desc.get_style()
        if sty != Pango.Style.NORMAL:
            return False  # avoid italic etc.
        weight = desc.get_weight()
        if weight != Pango.Weight.NORMAL:
            return False  # avoid Bold
        return True

    #-------------------------------------------------------------------------
    #
    # Printing functionalities
    #
    #-------------------------------------------------------------------------
    def printview(self, *obj):
        """
        Save the dot file for a later printing with an appropriate tool.
        """
        # ask for the dot file name
        filter1 = Gtk.FileFilter()
        filter1.set_name("dot files")
        filter1.add_pattern("*.gv")
        dot = Gtk.FileChooserDialog(title=_("Select a dot file name"),
                                    action=Gtk.FileChooserAction.SAVE,
                                    transient_for=self.uistate.window)
        dot.add_button(_('_Cancel'), Gtk.ResponseType.CANCEL)
        dot.add_button(_('_Apply'), Gtk.ResponseType.OK)
        mpath = config.get('paths.report-directory')
        dot.set_current_folder(os.path.dirname(mpath))
        dot.set_filter(filter1)
        dot.set_current_name("Graphview.gv")

        status = dot.run()
        if status == Gtk.ResponseType.OK:
            val = dot.get_filename()
            (spath, _ext) = os.path.splitext(val)
            val = spath + ".gv"  # used to avoid filename without extension
            # selected path is an existing file and we need a file
            if os.path.isfile(val):
                aaa = OptionDialog(_('File already exists'),  # parent-OK
                                   _('You can choose to either overwrite the '
                                     'file, or change the selected filename.'),
                                   _('_Overwrite'), None,
                                   _('_Change filename'), None,
                                   parent=dot)

                if aaa.get_response() == Gtk.ResponseType.YES:
                    dot.destroy()
                    self.printview(obj)
                    return
            svg = val.replace('.gv', '.svg')
            # both dot_data and svg_data are bytes, already utf-8 encoded
            # just write them as binary
            try:
                with open(val, 'wb') as __g, open(svg, 'wb') as __s:
                    __g.write(self.graph_widget.dot_data)
                    __s.write(self.graph_widget.svg_data)
            except IOError as msg:
                msg2 = _("Could not create %s") % (val + ', ' + svg)
                ErrorDialog(msg2, str(msg), parent=dot)
        dot.destroy()


#-------------------------------------------------------------------------
#
# GraphWidget
#
#-------------------------------------------------------------------------
class GraphWidget(object):
    """
    Define the widget with controls and canvas that displays the graph.
    """
    def __init__(self, view, dbstate, uistate):
        """
        :type view: GraphView
        """
        # variables for drag and scroll
        self._last_x = 0
        self._last_y = 0
        self._in_move = False
        self.view = view
        self.dbstate = dbstate
        self.uistate = uistate
        self.parser = None
        self.active_person_handle = None

        self.actions = Actions(dbstate, uistate, self.view.bookmarks)
        self.actions.connect('rebuild-graph', self.view.build_tree)
        self.actions.connect('active-changed', self.populate)
        self.actions.connect('focus-person-changed', self.set_person_to_focus)
        self.actions.connect('path-to-home-person', self.populate)

        self.dot_data = None
        self.svg_data = None

        scrolled_win = Gtk.ScrolledWindow()
        scrolled_win.set_shadow_type(Gtk.ShadowType.IN)
        self.hadjustment = scrolled_win.get_hadjustment()
        self.vadjustment = scrolled_win.get_vadjustment()

        self.canvas = GooCanvas.Canvas()
        self.canvas.connect("scroll-event", self.scroll_mouse)
        self.canvas.props.units = Gtk.Unit.POINTS
        self.canvas.props.resolution_x = 72
        self.canvas.props.resolution_y = 72

        scrolled_win.add(self.canvas)

        self.vbox = Gtk.Box(homogeneous=False, spacing=4,
                            orientation=Gtk.Orientation.VERTICAL)
        self.vbox.set_border_width(4)
        self.toolbar = Gtk.Box(homogeneous=False, spacing=4,
                               orientation=Gtk.Orientation.HORIZONTAL)
        self.vbox.pack_start(self.toolbar, False, False, 0)

        # add zoom-in button
        self.zoom_in_btn = Gtk.Button.new_from_icon_name('zoom-in',
                                                         Gtk.IconSize.MENU)
        self.zoom_in_btn.set_tooltip_text(_('Zoom in'))
        self.toolbar.pack_start(self.zoom_in_btn, False, False, 1)
        self.zoom_in_btn.connect("clicked", self.zoom_in)

        # add zoom-out button
        self.zoom_out_btn = Gtk.Button.new_from_icon_name('zoom-out',
                                                          Gtk.IconSize.MENU)
        self.zoom_out_btn.set_tooltip_text(_('Zoom out'))
        self.toolbar.pack_start(self.zoom_out_btn, False, False, 1)
        self.zoom_out_btn.connect("clicked", self.zoom_out)

        # add original zoom button
        self.orig_zoom_btn = Gtk.Button.new_from_icon_name('zoom-original',
                                                           Gtk.IconSize.MENU)
        self.orig_zoom_btn.set_tooltip_text(_('Zoom to original'))
        self.toolbar.pack_start(self.orig_zoom_btn, False, False, 1)
        self.orig_zoom_btn.connect("clicked", self.set_original_zoom)

        # add best fit button
        self.fit_btn = Gtk.Button.new_from_icon_name('zoom-fit-best',
                                                     Gtk.IconSize.MENU)
        self.fit_btn.set_tooltip_text(_('Zoom to best fit'))
        self.toolbar.pack_start(self.fit_btn, False, False, 1)
        self.fit_btn.connect("clicked", self.fit_to_page)

        # add 'go to active person' button
        self.goto_active_btn = Gtk.Button.new_from_icon_name('go-jump',
                                                             Gtk.IconSize.MENU)
        self.goto_active_btn.set_tooltip_text(_('Go to active person'))
        self.toolbar.pack_start(self.goto_active_btn, False, False, 1)
        self.goto_active_btn.connect("clicked", self.goto_active)

        # add 'go to bookmark' button
        self.goto_other_btn = Gtk.Button(label=_('Go to bookmark'))
        self.goto_other_btn.set_tooltip_text(
            _('Center view on selected bookmark'))
        self.toolbar.pack_start(self.goto_other_btn, False, False, 1)
        self.bkmark_popover = Popover(_('Bookmarks for current graph'),
                                      _('Other Bookmarks'),
                                      ext_panel=self.build_bkmark_ext_panel())
        self.bkmark_popover.set_relative_to(self.goto_other_btn)
        self.goto_other_btn.connect("clicked", self.show_bkmark_popup)
        self.goto_other_btn.connect("key-press-event",
                                    self.goto_other_btn_key_press_event)
        self.bkmark_popover.connect('item-activated', self.activate_popover)
        self.show_images_option = self.view._config.get(
            'interface.graphview-search-show-images')

        # add search widget
        self.search_widget = SearchWidget(self.dbstate,
                                          self.get_person_image,
                                          bookmarks=self.view.bookmarks)
        search_box = self.search_widget.get_widget()
        self.toolbar.pack_start(search_box, True, True, 1)
        self.search_widget.set_options(
            search_all_db=self.view._config.get(
                'interface.graphview-search-all-db'),
            show_images=self.show_images_option)
        self.search_widget.connect('item-activated', self.activate_popover)

        # Keep references to toolbar spinners so their visible
        # values can be updated after Load profile... changes config values.
        # Must be created before build_spinner() is called below.
        self.config_spinners = {}
        self.updating_profile_controls = False

        # add accelerator to focus search entry
        accel_group = Gtk.AccelGroup()
        self.uistate.window.add_accel_group(accel_group)
        search_box.add_accelerator('grab-focus', accel_group, Gdk.KEY_f,
                                   Gdk.ModifierType.CONTROL_MASK,
                                   Gtk.AccelFlags.VISIBLE)

        # add spinners for quick generations change
        gen_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        box = self.build_spinner('go-up-symbolic', 0, 50,
                                 _('Ancestor generations'),
                                 'interface.graphview-ancestor-generations')
        gen_box.add(box)
        box = self.build_spinner('go-down-symbolic', 0, 50,
                                 _('Descendant generations'),
                                 'interface.graphview-descendant-generations')
        gen_box.add(box)
        # pack generation spinners to popover
        gen_btn = Gtk.Button(label=_('Generations'))
        self.add_popover(gen_btn, gen_box)
        self.toolbar.pack_start(gen_btn, False, False, 1)

        # add spiner for generation (vertical) spacing
        spacing_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        box = self.build_spinner('object-flip-vertical', 1, 50,
                                 _('Vertical spacing between generations'),
                                 'interface.graphview-ranksep')
        spacing_box.add(box)
        # add spiner for node (horizontal) spacing
        box = self.build_spinner('object-flip-horizontal', 1, 50,
                                 _('Horizontal spacing between generations'),
                                 'interface.graphview-nodesep')
        spacing_box.add(box)
        # pack spacing spinners to popover
        spacing_btn = Gtk.Button(label=_('Spacings'))
        self.add_popover(spacing_btn, spacing_box)
        self.toolbar.pack_start(spacing_btn, False, False, 1)

        # add button to show all connected persons
        self.all_connected_btn = Gtk.ToggleButton(label=_('All connected'))
        self.all_connected_btn.set_tooltip_text(
            _("Show all connected persons limited by generation restrictions.\n"
              "Works slow, so don't set large generation values."))
        self.all_connected_btn.set_active(
            self.view._config.get('interface.graphview-show-all-connected'))
        self.all_connected_btn.connect('clicked', self.toggle_all_connected)
        self.toolbar.pack_start(self.all_connected_btn, False, False, 1)

        self.vbox.pack_start(scrolled_win, True, True, 0)

        # if we have graph lager than graphviz paper size
        # this coef is needed
        self.transform_scale = 1
        self.scale = self.view._config.get('interface.graphview-scale')

        self.animation = CanvasAnimation(self.view, self.canvas, scrolled_win)
        self.search_widget.set_items_list(self.animation.items_list)

        # person that will focus (once) after graph rebuilding
        self.person_to_focus = None

        # for detecting double click
        self.click_events = []

        # for timeout on changing settings by spinners
        self.timeout_event = False

        # Gtk style context for scrollwindow to operate with theme colors
        self.sw_style_context = scrolled_win.get_style_context()

        # used for popup menu, prevent destroy menu as local variable
        self.menu = None
        self.retest_font = True     # flag indicates need to resize font
        self.bold_size = self.norm_size = 0  # font sizes to send to dot

    def add_popover(self, widget, container):
        """
        Add popover for button.
        """
        popover = Gtk.Popover()
        popover.set_relative_to(widget)
        popover.add(container)
        widget.connect("clicked", self.spinners_popup, popover)
        container.show_all()

    def build_spinner(self, icon, start, end, tooltip, conf_const):
        """
        Build spinner with icon and pack it into box.
        Chenges apply to config with delay.
        """
        box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL)
        img = Gtk.Image.new_from_icon_name(icon, Gtk.IconSize.MENU)
        box.pack_start(img, False, False, 1)
        spinner = Gtk.SpinButton.new_with_range(start, end, 1)
        spinner.set_tooltip_text(tooltip)
        spinner.set_value(self.view._config.get(conf_const))
        spinner.connect("value-changed", self.apply_spinner_delayed,
                        conf_const)
        self.config_spinners[conf_const] = spinner
        box.pack_start(spinner, False, False, 1)
        return box

    def toggle_all_connected(self, widget):
        """
        Change state for "Show all connected" setting.
        """
        self.view._config.set('interface.graphview-show-all-connected',
                              widget.get_active())

    def spinners_popup(self, _widget, popover):
        """
        Popover for generations and spacing params.
        Different popup depending on gtk version.
        """
        if gtk_version >= 3.22:
            popover.popup()
        else:
            popover.show()

    def set_available(self, state):
        """
        Set state for GraphView.
        """
        if not state:
            # if no database is opened
            self.clear()
        self.toolbar.set_sensitive(state)

    def font_changed(self, active):
        self.sym_font = config.get('utf8.selected-font')
        if self.parser:
            self.parser.font_changed()
            self.populate(active)

    def set_person_to_focus(self, handle):
        """
        Set person that will focus (once) after graph rebuilding.
        """
        self.person_to_focus = handle

    def goto_other_btn_key_press_event(self, _widget, event):
        """
        Handle 'Esc' key on bookmarks button to hide popup.
        """
        key = event.keyval
        if event.keyval == Gdk.KEY_Escape:
            self.hide_bkmark_popover()
        elif key == Gdk.KEY_Down:
            self.bkmark_popover.grab_focus()
            return True

    def activate_popover(self, _widget, person_handle):
        """
        Called when some item(person)
        in search or bookmarks popup(popover) is activated.
        """
        self.hide_bkmark_popover()
        self.search_widget.hide_search_popover()
        # move view to person with animation
        self.move_to_person(None, person_handle, True)

    def apply_spinner_delayed(self, widget, conf_const):
        """
        Set params by spinners (generations, spacing).
        Use timeout for better interface responsiveness.
        """
        if getattr(self, 'updating_profile_controls', False):
            return

        value = int(widget.get_value())
        # try to remove planed event (changing setting)
        if self.timeout_event and \
                not self.timeout_event.is_destroyed():
            GLib.source_remove(self.timeout_event.get_id())
        # timeout saving setting for better interface responsiveness
        event_id = GLib.timeout_add(300, self.view._config.set,
                                    conf_const, value)
        context = GLib.main_context_default()
        self.timeout_event = context.find_source_by_id(event_id)

    def cancel_pending_spinner_update(self):
        """
        Cancel a delayed Generations/Spacings write that has not run yet.

        The toolbar spin buttons save through one shared 300 ms timeout.
        Temp restore must cancel it before applying the opening snapshot,
        otherwise the delayed callback can overwrite the restored value.
        """
        timeout_event = getattr(self, 'timeout_event', False)
        if timeout_event and not timeout_event.is_destroyed():
            GLib.source_remove(timeout_event.get_id())
        self.timeout_event = False

    def sync_profile_controls(self):
        """
        Update toolbar controls after profile values have been loaded.
        The checks make startup safe if Graph View is not fully built yet.
        """
        if not hasattr(self, 'config_spinners'):
            return False

        self.updating_profile_controls = True
        try:
            for config_key, spinner in self.config_spinners.items():
                if spinner is not None:
                    spinner.set_value(self.view._config.get(config_key))

            all_connected_btn = getattr(self, 'all_connected_btn', None)
            if all_connected_btn is not None:
                all_connected_btn.set_active(
                    self.view._config.get(
                        'interface.graphview-show-all-connected'))
        finally:
            self.updating_profile_controls = False

        return False

    def restore_profile_view_state(self, view_state):
        """
        Restore optional view state after the graph has been rebuilt.
        This is intentionally separate from graph/profile content settings.
        """
        if not isinstance(view_state, dict):
            return False

        scale = view_state.get('interface.graphview-scale')
        if scale is not None:
            try:
                self.set_zoom(float(scale))
            except (TypeError, ValueError):
                pass

        h_value = view_state.get('horizontal_adjustment_value')
        v_value = view_state.get('vertical_adjustment_value')

        def clamp_adjustment(adjustment, value):
            if value is None:
                return
            try:
                value = float(value)
            except (TypeError, ValueError):
                return
            lower = adjustment.get_lower()
            upper = adjustment.get_upper() - adjustment.get_page_size()
            if upper < lower:
                upper = lower
            adjustment.set_value(max(lower, min(value, upper)))

        clamp_adjustment(self.hadjustment, h_value)
        clamp_adjustment(self.vadjustment, v_value)

        return False

    def build_bkmark_ext_panel(self):
        """
        Build bookmark popover extand panel.
        """
        btn_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL)
        # add button to add active person to bookmarks
        # tooltip will be changed in "self.load_bookmarks"
        self.add_bkmark = Gtk.Button(label=_('Add active person'))
        self.add_bkmark.connect("clicked", self.add_active_to_bkmarks)
        btn_box.pack_start(self.add_bkmark, True, True, 2)
        # add buton to call bookmarks manager
        manage_bkmarks = Gtk.Button(label=_('Edit'))
        manage_bkmarks.set_tooltip_text(_('Call the bookmark editor'))
        manage_bkmarks.connect("clicked", self.edit_bookmarks)
        btn_box.pack_start(manage_bkmarks, True, True, 2)
        return btn_box

    def load_bookmarks(self):
        """
        Load bookmarks in Popover (goto_other_btn).
        """
        # remove all old items from popup
        self.bkmark_popover.clear_items()

        active = self.view.get_active()
        active_in_bkmarks = False
        found = False
        found_other = False
        count = 0
        count_other = 0

        bookmarks = self.view.bookmarks.get_bookmarks().bookmarks
        for bkmark in bookmarks:
            if active == bkmark:
                active_in_bkmarks = True
            person = self.dbstate.db.get_person_from_handle(bkmark)
            if person:
                name = displayer.display_name(person.get_primary_name())
                present = self.animation.get_item_by_title(bkmark)

                hbox = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL,
                               spacing=10)
                # add person ID
                label = Gtk.Label("[%s]" % person.gramps_id, xalign=0)
                hbox.pack_start(label, False, False, 2)
                # add person name
                label = Gtk.Label(name, xalign=0)
                hbox.pack_start(label, True, True, 2)
                # add person image if needed
                if self.show_images_option:
                    person_image = self.get_person_image(person, 32, 32)
                    if person_image:
                        hbox.pack_start(person_image, False, True, 2)
                row = ListBoxRow(person_handle=bkmark, label=name,
                                 db=self.dbstate.db)
                row.add(hbox)

                if present is not None:
                    found = True
                    count += 1
                    self.bkmark_popover.main_panel.add_to_panel(row)
                else:
                    found_other = True
                    count_other += 1
                    self.bkmark_popover.other_panel.add_to_panel(row)
                row.show_all()
        if not found and not found_other:
            self.bkmark_popover.show_other_panel(False)
            row = ListBoxRow()
            row.add(Gtk.Label(_("You don't have any bookmarks yet...\n"
                                "Try to add some frequently used persons "
                                "to speedup navigation.")))
            self.bkmark_popover.main_panel.add_to_panel(row)
            row.show_all()
        else:
            if not found:
                row = ListBoxRow()
                row.add(Gtk.Label(_('No bookmarks for this graph...')))
                self.bkmark_popover.main_panel.add_to_panel(row)
                row.show_all()
            if not found_other:
                row = ListBoxRow()
                row.add(Gtk.Label(_('No other bookmarks...')))
                self.bkmark_popover.other_panel.add_to_panel(row)
                row.show_all()
                self.bkmark_popover.show_other_panel(True)

        self.bkmark_popover.main_panel.set_progress(0, _('found: %s') % count)
        self.bkmark_popover.other_panel.set_progress(
            0, _('found: %s') % count_other)

        # set tooltip for "add_bkmark" button
        self.add_bkmark.hide()
        if active and not active_in_bkmarks:
            person = self.dbstate.db.get_person_from_handle(active)
            if person:
                name = displayer.display_name(person.get_primary_name())
                val_to_display = "[%s] %s" % (person.gramps_id, name)
                self.add_bkmark.set_tooltip_text(
                    _('Add active person to bookmarks\n'
                      '%s') % val_to_display)
                self.add_bkmark.show()

    def get_person_image(self, person, width=-1, height=-1, kind='image'):
        """
        kind - 'image', 'path', 'both'
        Returns default person image and path or None.
        """
        # see if we have an image to use for this person
        image_path = None
        media_list = person.get_media_list()
        if media_list:
            media_handle = media_list[0].get_reference_handle()
            media = self.dbstate.db.get_media_from_handle(media_handle)
            media_mime_type = media.get_mime_type()
            if media_mime_type[0:5] == "image":
                rectangle = media_list[0].get_rectangle()
                path = media_path_full(self.dbstate.db, media.get_path())
                image_path = get_thumbnail_path(path, rectangle=rectangle)
                # test if thumbnail actually exists in thumbs
                # (import of data means media files might not be present
                image_path = find_file(image_path)
        if image_path:
            if kind == 'path':
                return image_path
            # get and scale image
            person_image = GdkPixbuf.Pixbuf.new_from_file_at_scale(
                filename=image_path,
                width=width, height=height,
                preserve_aspect_ratio=True)
            person_image = Gtk.Image.new_from_pixbuf(person_image)
            if kind == 'image':
                return person_image
            elif kind == 'both':
                return person_image, image_path

        return None

    def add_active_to_bkmarks(self, _widget):
        """
        Add active person to bookmarks.
        """
        self.view.add_bookmark(None)
        self.load_bookmarks()

    def edit_bookmarks(self, _widget):
        """
        Call the bookmark editor.
        """
        self.view.edit_bookmarks(None)
        self.load_bookmarks()

    def show_bkmark_popup(self, _widget):
        """
        Show bookmark popup.
        """
        self.load_bookmarks()
        self.bkmark_popover.popup()

    def hide_bkmark_popover(self, _widget=None, _event=None):
        """
        Hide bookmark popup.
        """
        self.bkmark_popover.popdown()

    def goto_active(self, button=None):
        """
        Go to active person.
        """
        # check if animation is needed
        animation = bool(button)
        self.animation.move_to_person(self.active_person_handle, animation)

    def move_to_person(self, _menuitem, handle, animate=False):
        """
        Move to specified person (by handle).
        If person not present in the current graphview tree,
        show dialog to change active person.
        """
        self.person_to_focus = None
        if self.animation.get_item_by_title(handle):
            self.animation.move_to_person(handle, animate)
        else:
            person = self.dbstate.db.get_person_from_handle(handle)
            if not person:
                return False
            quest = (_('Person <b><i>%s</i></b> is not in the current view.\n'
                       'Do you want to set it active and rebuild view?')
                     % escape(displayer.display(person)))
            dialog = QuestionDialog2(_("Change active person?"), quest,
                                     _("Yes"), _("No"),
                                     self.uistate.window)
            if dialog.run():
                self.view.change_active(handle)

    def scroll_mouse(self, _canvas, event):
        """
        Zoom by mouse wheel.
        """
        if event.direction == Gdk.ScrollDirection.UP:
            self.zoom_in()
        elif event.direction == Gdk.ScrollDirection.DOWN:
            self.zoom_out()

        # stop the signal of scroll emission
        # to prevent window scrolling
        return True

    def populate(self, active_person, path_to_home_person=False):
        """
        Populate the graph with widgets derived from Graphviz.
        """
        # Config callbacks and active-person signals may request
        # many rebuilds while a profile is being applied. Ignore all of those;
        # the outer profile function performs one final populate when ready.
        if getattr(self.view, '_profile_graph_refresh_depth', 0) > 0:
            return

        # This is a final passive safety net. Ordinary
        # book opening must never warn because of a value left by another
        # book. Manual activation and profile loading still show their own
        # clear warning when ProfileTag is missing.
        if self.view.turn_off_family_tag_filter_for_missing_tag(
                show_warning=False):
            pass

        # set the busy cursor, so the user knows that we are working
        self.uistate.set_busy_cursor(True)
        if self.uistate.window.get_window().is_visible():
            process_pending_events()

        self.clear()
        self.active_person_handle = active_person

        # fit the text to boxes
        self.bold_size, self.norm_size = self.fit_text()

        self.search_widget.hide_search_popover()
        self.hide_bkmark_popover()

        # generate DOT and SVG data
        dot = DotSvgGenerator(self.dbstate, self.view,
                              bold_size=self.bold_size,
                              norm_size=self.norm_size)

        graph_data = dot.build_graph(active_person, path_to_home_person)
        del dot

        if not graph_data:
            # something go wrong when build all-connected tree
            # so turn off this feature
            self.view._config.set('interface.graphview-show-all-connected',
                                  False)
            return

        self.dot_data = graph_data[0]
        self.svg_data = graph_data[1]

        parser = GraphvizSvgParser(self, self.view)
        parser.parse(self.svg_data)

        self.animation.update_items(parser.items_list)

        # save transform scale
        self.transform_scale = parser.transform_scale
        self.set_zoom(self.scale)

        # focus on edited person if posible
        if not self.animation.move_to_person(self.person_to_focus, False):
            self.goto_active()
        self.person_to_focus = None

        # update the status bar
        self.view.change_page()

        self.uistate.set_busy_cursor(False)

    def zoom_in(self, _button=None):
        """
        Increase zoom scale.
        """
        scale_coef = self.scale * 1.1
        self.set_zoom(scale_coef)

    def zoom_out(self, _button=None):
        """
        Decrease zoom scale.
        """
        scale_coef = self.scale * 0.9
        if scale_coef < 0.01:
            scale_coef = 0.01
        self.set_zoom(scale_coef)

    def set_original_zoom(self, _button):
        """
        Set original zoom scale = 1.
        """
        self.set_zoom(1)

    def fit_to_page(self, _button):
        """
        Calculate scale and fit tree to page.
        """
        # get the canvas size
        bounds = self.canvas.get_root_item().get_bounds()
        height_canvas = bounds.y2 - bounds.y1
        width_canvas = bounds.x2 - bounds.x1

        # get scroll window size
        width = self.hadjustment.get_page_size()
        height = self.vadjustment.get_page_size()

        # prevent division by zero
        if height_canvas == 0:
            height_canvas = 1
        if width_canvas == 0:
            width_canvas = 1

        # calculate minimum scale
        scale_h = (height / height_canvas)
        scale_w = (width / width_canvas)
        if scale_h > scale_w:
            scale = scale_w
        else:
            scale = scale_h

        scale = scale * self.transform_scale

        # set scale if it needed, else restore it to default
        if scale < 1:
            self.set_zoom(scale)
        else:
            self.set_zoom(1)

    def clear(self):
        """
        Clear the graph by creating a new root item.
        """
        # remove root item (with all children)
        self.canvas.get_root_item().remove()
        self.canvas.set_root_item(GooCanvas.CanvasGroup())

    def get_widget(self):
        """
        Return the graph display widget that includes the drawing canvas.
        """
        return self.vbox

    def button_press(self, item, _target, event):
        """
        Enter in scroll mode when left or middle mouse button pressed
        on background.
        """
        self.search_widget.hide_search_popover()
        self.hide_bkmark_popover()

        if not (event.type == getattr(Gdk.EventType, "BUTTON_PRESS") and
                item == self.canvas.get_root_item()):
            return False

        button = event.get_button()[1]
        if button == 1 or button == 2:
            window = self.canvas.get_parent().get_window()
            window.set_cursor(Gdk.Cursor.new(Gdk.CursorType.FLEUR))
            self._last_x = event.x_root
            self._last_y = event.y_root
            self._in_move = True
            self.animation.stop_animation()
            return False

        if button == 3:
            self.menu = PopupMenu(self, kind='background')
            self.menu.show_menu(event)
            return True

        return False

    def button_release(self, item, target, event):
        """
        Exit from scroll mode when button release.
        """
        button = event.get_button()[1]
        if((button == 1 or button == 2) and
           event.type == getattr(Gdk.EventType, "BUTTON_RELEASE")):

            self.motion_notify_event(item, target, event)
            self.canvas.get_parent().get_window().set_cursor(None)
            self._in_move = False
            return True
        return False

    def motion_notify_event(self, _item, _target, event):
        """
        Function for motion notify events for drag and scroll mode.
        """
        if self._in_move and (event.type == Gdk.EventType.MOTION_NOTIFY or
                              event.type == Gdk.EventType.BUTTON_RELEASE):

            # scale coefficient for prevent flicking when drag
            scale_coef = self.canvas.get_scale()

            new_x = (self.hadjustment.get_value() -
                     (event.x_root - self._last_x) * scale_coef)
            self.hadjustment.set_value(new_x)

            new_y = (self.vadjustment.get_value() -
                     (event.y_root - self._last_y) * scale_coef)
            self.vadjustment.set_value(new_y)
            return True
        return False

    def set_zoom(self, value):
        """
        Set value for zoom of the canvas widget and apply it.
        """
        self.scale = value
        self.view._config.set('interface.graphview-scale', value)
        self.canvas.set_scale(value / self.transform_scale)

    def select_node(self, item, target, event):
        """
        Perform actions when a node is clicked.
        If middle mouse was clicked then try to set scroll mode.
        """
        self.search_widget.hide_search_popover()
        self.hide_bkmark_popover()

        handle = item.title
        node_class = item.description
        button = event.get_button()[1]

        self.person_to_focus = None

        # perform double click on node by left mouse button
        if event.type == getattr(Gdk.EventType, "DOUBLE_BUTTON_PRESS"):
            # Remove all single click events
            for click_item in self.click_events:
                if not click_item.is_destroyed():
                    GLib.source_remove(click_item.get_id())
            self.click_events.clear()
            if button == 1 and node_class == 'node':
                GLib.idle_add(self.actions.edit_person, None, handle)
                return True
            elif button == 1 and node_class == 'familynode':
                GLib.idle_add(self.actions.edit_family, None, handle)
                return True

        if event.type != getattr(Gdk.EventType, "BUTTON_PRESS"):
            return False

        if button == 1 and node_class == 'node':            # left mouse
            if handle == self.active_person_handle:
                # Find a parent of the active person so that they can become
                # the active person, if no parents then leave as the current
                # active person
                parent_handle = self.find_a_parent(handle)
                if parent_handle:
                    handle = parent_handle
                else:
                    return True

            # redraw the graph based on the selected person
            # schedule after because double click can occur
            click_event_id = GLib.timeout_add(200, self.view.change_active,
                                              handle)
            # add single click events to list, it will be removed if necessary
            context = GLib.main_context_default()
            self.click_events.append(context.find_source_by_id(click_event_id))

        elif button == 3 and node_class:                    # right mouse
            if node_class == 'node':
                self.menu = PopupMenu(self, 'person', handle)
                self.menu.show_menu(event)
            elif node_class == 'familynode':
                self.menu = PopupMenu(self, 'family', handle)
                self.menu.show_menu(event)

        elif button == 2:                                   # middle mouse
            # to enter in scroll mode (we should change "item" to root item)
            item = self.canvas.get_root_item()
            self.button_press(item, target, event)

        return True

    def find_a_parent(self, handle):
        """
        Locate a parent from the first family that the selected person is a
        child of. Try and find the father first, then the mother.
        Either will be OK.
        """
        person = self.dbstate.db.get_person_from_handle(handle)
        try:
            fam_handle = person.get_parent_family_handle_list()[0]
            if fam_handle:
                family = self.dbstate.db.get_family_from_handle(fam_handle)
                if family and family.get_father_handle():
                    handle = family.get_father_handle()
                elif family and family.get_mother_handle():
                    handle = family.get_mother_handle()
        except IndexError:
            handle = None

        return handle

    def update_lines_type(self, _menu_item, lines_type, constant):
        """
        Save the lines type setting.
        """
        self.view._config.set(constant, lines_type)

    def update_setting(self, menu_item, constant):
        """
        Save changed setting.
        menu_item should be Gtk.CheckMenuItem.
        """
        value = menu_item.get_active()
        if (constant == 'interface.graphview-filter-family-tag' and
                value and
                not self.view.family_tag_filter_value_is_allowed(True)):
            menu_item.set_active(False)
            value = False
        self.view._config.set(constant, value)
        
    def fit_text(self):
        """
        Fit the text to the boxes more exactly.  Works by trying some sample
        text, measuring the results, and trying an increasing size of font
        sizes to some sample nodes to see which one will fit the expected
        text size.
        In other words we are telling dot to use different font sizes than
        we are actually displaying, since dot doesn't do a good job of
        determining the text size.
        """
        if not self.retest_font:  # skip this uless font changed.
            return self.bold_size, self.norm_size

        text = "The quick Brown Fox jumped over the Lazy Dogs 1948-01-01."
        dot_test = DotSvgGenerator(self.dbstate, self.view)
        dot_test.init_dot()
        # These are at the desired font sizes.
        dot_test.add_node('test_bold', '<B>%s</B>' % text, shape='box')
        dot_test.add_node('test_norm', text, shape='box')
        # now add nodes at increasing font sizes
        for scale in range(35, 140, 2):
            f_size = dot_test.fontsize * scale / 100.0
            dot_test.add_node(
                'test_bold' + str(scale),
                '<FONT POINT-SIZE="%(bsize)3.1f"><B>%(text)s</B></FONT>' %
                {'text': text, 'bsize': f_size}, shape='box')
            dot_test.add_node(
                'test_norm' + str(scale),
                text, shape='box', fontsize=("%3.1f" % f_size))

        # close the graphviz dot code with a brace
        dot_test.write('}\n')

        # get DOT and generate SVG data by Graphviz
        dot_data = dot_test.dot.getvalue().encode('utf8')
        svg_data = dot_test.make_svg(dot_data)
        svg_data = svg_data.decode('utf8')

        # now lest find the box sizes, and font sizes for the generated svg.
        points_a = findall(r'points="(.*)"', svg_data, MULTILINE)
        font_fams = findall(r'font-family="(.*)" font-weight',
                            svg_data, MULTILINE)
        font_sizes = findall(r'font-size="(.*)" fill', svg_data, MULTILINE)
        box_w = []
        for points in points_a:
            box_pts = points.split()
            x_1 = box_pts[0].split(',')[0]
            x_2 = box_pts[1].split(',')[0]
            box_w.append(float(x_1) - float(x_2) - 16)  # adjust for margins

        text_font = font_fams[0] + ", " + font_sizes[0] + 'px'
        font_desc = Pango.FontDescription.from_string(text_font)

        # lets measure the bold text on our canvas at desired font size
        c_text = GooCanvas.CanvasText(parent=self.canvas.get_root_item(),
                                      text='<b>' + text + '</b>',
                                      x=100,
                                      y=100,
                                      anchor=GooCanvas.CanvasAnchorType.WEST,
                                      use_markup=True,
                                      font_desc=font_desc)
        bold_b = c_text.get_bounds()
        # and measure the normal text on our canvas at desired font size
        c_text.props.text = text
        norm_b = c_text.get_bounds()
        # now scan throught test boxes, finding the smallest that will hold
        # the actual text as measured.  And record the dot font that was used.
        for indx in range(3, len(font_sizes), 2):
            bold_size = float(font_sizes[indx - 1])
            if box_w[indx] > bold_b.x2 - bold_b.x1:
                break
        for indx in range(4, len(font_sizes), 2):
            norm_size = float(font_sizes[indx - 1])
            if box_w[indx] > norm_b.x2 - norm_b.x1:
                break
        self.retest_font = False  # we don't do this again until font changes
        # return the adjusted font size to tell dot to use.
        return bold_size, norm_size


#-------------------------------------------------------------------------
#
# GraphvizSvgParser
#
#-------------------------------------------------------------------------
class GraphvizSvgParser(object):
    """
    Parses SVG produces by Graphviz and adds the elements to a GooCanvas.
    """

    def __init__(self, widget, view):
        """
        Initialise the GraphvizSvgParser class.
        """
        self.func = None
        self.widget = widget
        self.canvas = widget.canvas
        self.view = view
        self.highlight_home_person = self.view._config.get(
            'interface.graphview-highlight-home-person')
        scheme = config.get('colors.scheme')
        self.home_person_color = config.get('colors.home-person')[scheme]
        self.font_size = self.view._config.get('interface.graphview-font')[1]
        self.active_person_border_size = self.view._config.get(
            'interface.graphview-active-person-border-size')
        self.person_border_size = self.view._config.get(
            'interface.graphview-person-border-size')

        self.tlist = []
        self.text_attrs = None
        self.func_list = []
        self.handle = None
        self.func_map = {"g":       (self.start_g, self.stop_g),
                         "svg":     (self.start_svg, self.stop_svg),
                         "polygon": (self.start_polygon, self.stop_polygon),
                         "path":    (self.start_path, self.stop_path),
                         "image":   (self.start_image, self.stop_image),
                         "text":    (self.start_text, self.stop_text),
                         "ellipse": (self.start_ellipse, self.stop_ellipse),
                         "title":   (self.start_title, self.stop_title)}
        self.text_anchor_map = {"start":  GooCanvas.CanvasAnchorType.WEST,
                                "middle": GooCanvas.CanvasAnchorType.CENTER,
                                "end":    GooCanvas.CanvasAnchorType.EAST}
        # This list is used as a LIFO stack so that the SAX parser knows
        # which Goocanvas object to link the next object to.
        self.item_hier = []

        # list of persons items, used for animation class
        self.items_list = []

        self.transform_scale = 1

    def parse(self, ifile):
        """
        Parse an SVG file produced by Graphviz.
        """
        self.item_hier.append(self.canvas.get_root_item())
        parser = ParserCreate()
        parser.StartElementHandler = self.start_element
        parser.EndElementHandler = self.end_element
        parser.CharacterDataHandler = self.characters
        parser.Parse(ifile)

        for key in list(self.func_map.keys()):
            del self.func_map[key]
        del self.func_map
        del self.func_list
        del parser

    def start_g(self, attrs):
        """
        Parse <g> tags.
        """
        # The class attribute defines the group type. There should be one
        # graph type <g> tag which defines the transform for the whole graph.
        if attrs.get('class') == 'graph':
            self.items_list.clear()
            transform = attrs.get('transform')
            item = self.canvas.get_root_item()
            transform_list = transform.split(') ')
            scale = transform_list[0].split()
            scale_x = float(scale[0].lstrip('scale('))
            scale_y = float(scale[1])
            self.transform_scale = scale_x
            if scale_x > scale_y:
                self.transform_scale = scale_y
            # scale should be (0..1)
            # fix graphviz issue from version > 2.40.1
            if self.transform_scale > 1:
                self.transform_scale = 1 / self.transform_scale

            item.set_simple_transform(self.bounds[1],
                                      self.bounds[3],
                                      self.transform_scale,
                                      0)
            item.connect("button-press-event", self.widget.button_press)
            item.connect("button-release-event", self.widget.button_release)
            item.connect("motion-notify-event",
                         self.widget.motion_notify_event)
        else:
            item = GooCanvas.CanvasGroup(parent=self.current_parent())
            item.connect("button-press-event", self.widget.select_node)
            self.items_list.append(item)

        item.description = attrs.get('class')
        self.item_hier.append(item)

    def stop_g(self, _tag):
        """
        Parse </g> tags.
        """
        item = self.item_hier.pop()
        item.title = self.handle

    def start_svg(self, attrs):
        """
        Parse <svg> tags.
        """
        GooCanvas.CanvasGroup(parent=self.current_parent())

        view_box = attrs.get('viewBox').split()
        v_left = float(view_box[0])
        v_top = float(view_box[1])
        v_right = float(view_box[2])
        v_bottom = float(view_box[3])
        self.canvas.set_bounds(v_left, v_top, v_right, v_bottom)
        self.bounds = (v_left, v_top, v_right, v_bottom)

    def stop_svg(self, tag):
        """
        Parse </svg> tags.
        """
        pass

    def start_title(self, attrs):
        """
        Parse <title> tags.
        """
        pass

    def stop_title(self, tag):
        """
        Parse </title> tags.
        Stripping off underscore prefix added to fool Graphviz.
        """
        self.handle = tag.lstrip("_")

    def start_polygon(self, attrs):
        """
        Parse <polygon> tags.
        Polygons define the boxes around individuals on the graph.
        """
        coord_string = attrs.get('points')
        coord_count = 5
        points = GooCanvas.CanvasPoints.new(coord_count)
        nnn = 0
        for i in coord_string.split():
            coord = i.split(",")
            coord_x = float(coord[0])
            coord_y = float(coord[1])
            points.set_point(nnn, coord_x, coord_y)
            nnn += 1
        style = attrs.get('style')

        if style:
            p_style = self.parse_style(style)
            stroke_color = p_style['stroke']
            fill_color = p_style['fill']
        else:
            stroke_color = attrs.get('stroke')
            fill_color = attrs.get('fill')

        if self.handle == self.widget.active_person_handle:
            line_width = self.active_person_border_size
        else:
            line_width = self.person_border_size

        tooltip = self.view.tags_tooltips.get(self.handle)

        # highlight the home person
        # stroke_color is not '#...' when tags are drawing, so we check this
        # maybe this is not good solution to check for tags but it works
        if self.highlight_home_person and stroke_color[:1] == '#':
            home_person = self.widget.dbstate.db.get_default_person()
            if home_person and home_person.handle == self.handle:
                fill_color = self.home_person_color

        item = GooCanvas.CanvasPolyline(parent=self.current_parent(),
                                        points=points,
                                        close_path=True,
                                        fill_color=fill_color,
                                        line_width=line_width,
                                        stroke_color=stroke_color,
                                        tooltip=tooltip)
        # turn on tooltip show if have it
        if tooltip:
            item_canvas = item.get_canvas()
            item_canvas.set_has_tooltip(True)

        self.item_hier.append(item)

    def stop_polygon(self, _tag):
        """
        Parse </polygon> tags.
        """
        self.item_hier.pop()

    def start_ellipse(self, attrs):
        """
        Parse <ellipse> tags.
        These define the family nodes of the graph.
        """
        center_x = float(attrs.get('cx'))
        center_y = float(attrs.get('cy'))
        radius_x = float(attrs.get('rx'))
        radius_y = float(attrs.get('ry'))
        style = attrs.get('style')

        if style:
            p_style = self.parse_style(style)
            stroke_color = p_style['stroke']
            fill_color = p_style['fill']
        else:
            stroke_color = attrs.get('stroke')
            fill_color = attrs.get('fill')

        tooltip = self.view.tags_tooltips.get(self.handle)

        item = GooCanvas.CanvasEllipse(parent=self.current_parent(),
                                       center_x=center_x,
                                       center_y=center_y,
                                       radius_x=radius_x,
                                       radius_y=radius_y,
                                       fill_color=fill_color,
                                       stroke_color=stroke_color,
                                       line_width=1,
                                       tooltip=tooltip)
        if tooltip:
            item_canvas = item.get_canvas()
            item_canvas.set_has_tooltip(True)

        self.current_parent().description = 'familynode'
        self.item_hier.append(item)

    def stop_ellipse(self, _tag):
        """
        Parse </ellipse> tags.
        """
        self.item_hier.pop()

    def start_path(self, attrs):
        """
        Parse <path> tags.
        These define the links between nodes.
        Solid lines represent birth relationships and dashed lines are used
        when a child has a non-birth relationship to a parent.
        """
        p_data = attrs.get('d')
        line_width = attrs.get('stroke-width')
        if line_width is None:
            line_width = 1
        line_width = float(line_width)
        style = attrs.get('style')

        if style:
            p_style = self.parse_style(style)
            stroke_color = p_style['stroke']
            is_dashed = 'stroke-dasharray' in p_style
        else:
            stroke_color = attrs.get('stroke')
            is_dashed = attrs.get('stroke-dasharray')

        if is_dashed:
            line_dash = GooCanvas.CanvasLineDash.newv([5.0, 5.0])
            item = GooCanvas.CanvasPath(parent=self.current_parent(),
                                        data=p_data,
                                        stroke_color=stroke_color,
                                        line_width=line_width,
                                        line_dash=line_dash)
        else:
            item = GooCanvas.CanvasPath(parent=self.current_parent(),
                                        data=p_data,
                                        stroke_color=stroke_color,
                                        line_width=line_width)
        self.item_hier.append(item)

    def stop_path(self, _tag):
        """
        Parse </path> tags.
        """
        self.item_hier.pop()

    def start_text(self, attrs):
        """
        Parse <text> tags.
        """
        self.text_attrs = attrs

    def stop_text(self, tag):
        """
        Parse </text> tags.
        The text tag contains some textual data.
        """
        tag = escape(tag)

        pos_x = float(self.text_attrs.get('x'))
        pos_y = float(self.text_attrs.get('y'))
        anchor = self.text_attrs.get('text-anchor')
        style = self.text_attrs.get('style')

        # does the following always work with symbols?
        if style:
            p_style = self.parse_style(style)
            font_family = p_style['font-family']
            text_font = font_family + ", " + p_style['font-size'] + 'px'
        else:
            font_family = self.text_attrs.get('font-family')
            text_font = font_family + ", " + str(self.font_size) + 'px'

        font_desc = Pango.FontDescription.from_string(text_font)

        # set bold text using PangoMarkup
        if self.text_attrs.get('font-weight') == 'bold':
            tag = '<b>%s</b>' % tag

        # text color
        fill_color = self.text_attrs.get('fill')

        GooCanvas.CanvasText(parent=self.current_parent(),
                             text=tag,
                             x=pos_x,
                             y=pos_y,
                             anchor=self.text_anchor_map[anchor],
                             use_markup=True,
                             font_desc=font_desc,
                             fill_color=fill_color)

    def start_image(self, attrs):
        """
        Parse <image> tags.
        """
        pos_x = float(attrs.get('x'))
        pos_y = float(attrs.get('y'))
        width = float(attrs.get('width').rstrip(string.ascii_letters))
        height = float(attrs.get('height').rstrip(string.ascii_letters))
        pixbuf = GdkPixbuf.Pixbuf.new_from_file(attrs.get('xlink:href'))

        item = GooCanvas.CanvasImage(parent=self.current_parent(),
                                     x=pos_x,
                                     y=pos_y,
                                     height=height,
                                     width=width,
                                     pixbuf=pixbuf)
        self.item_hier.append(item)

    def stop_image(self, _tag):
        """
        Parse </image> tags.
        """
        self.item_hier.pop()

    def start_element(self, tag, attrs):
        """
        Generic parsing function for opening tags.
        """
        self.func_list.append((self.func, self.tlist))
        self.tlist = []

        try:
            start_function, self.func = self.func_map[tag]
            if start_function:
                start_function(attrs)
        except KeyError:
            self.func_map[tag] = (None, None)
            self.func = None

    def end_element(self, _tag):
        """
        Generic parsing function for closing tags.
        """
        if self.func:
            self.func(''.join(self.tlist))
        self.func, self.tlist = self.func_list.pop()

    def characters(self, data):
        """
        Generic parsing function for tag data.
        """
        if self.func:
            self.tlist.append(data)

    def current_parent(self):
        """
        Returns the Goocanvas object which should be the parent of any new
        Goocanvas objects.
        """
        return self.item_hier[len(self.item_hier) - 1]

    def parse_style(self, style):
        """
        Parse style attributes for Graphviz version < 2.24.
        """
        style = style.rstrip(';')
        return dict([i.split(':') for i in style.split(';')])


#------------------------------------------------------------------------
#
# DotSvgGenerator
#
#------------------------------------------------------------------------
class DotSvgGenerator(object):
    """
    Generator of graphing instructions in dot format and svg data by Graphviz.
    """
    def __init__(self, dbstate, view, bold_size=0, norm_size=0):
        """
        Initialise the DotSvgGenerator class.
        """
        self.bold_size = bold_size
        self.norm_size = norm_size
        self.dbstate = dbstate
        self.uistate = view.uistate
        self.database = dbstate.db
        self.view = view

        self.dot = None         # will be StringIO()

        # This dictionary contains person handle as the index and the value is
        # the number of families in which the person is a parent. From this
        # dictionary is obtained a list of person handles sorted in decreasing
        # value order which is used to keep multiple spouses positioned
        # together.
        self.person_handles_dict = {}
        self.person_handles = []

        # list of persons on path to home person
        self.current_list = list()
        self.home_person = None

        # Gtk style context for scrollwindow
        self.context = self.view.graph_widget.sw_style_context

        # font if we use genealogical symbols
        self.sym_font = None

        self.avatars = Avatars(self.view._config)

    def __del__(self):
        """
        Free stream file on destroy.
        """
        if self.dot:
            self.dot.close()

    FAMILY_TAG = "ProfileTag"

    def has_family_tag(self, person):

        print("Filter:",
            self.view._config.get('interface.graphview-filter-family-tag'))

        if not self.view._config.get('interface.graphview-filter-family-tag'):
            return True

        if not person:
            return False

        for tag_handle in person.get_tag_list():
            tag = self.database.get_tag_from_handle(tag_handle)
            if tag and tag.get_name() == FAMILY_TAG:
                return True

        return False
        
    def init_dot(self):
        """
        Init/reinit stream for dot file.
        Load and write config data to start of dot file.
        """
        if self.dot:
            self.dot.close()
        self.dot = StringIO()

        self.current_list.clear()
        self.person_handles_dict.clear()

        self.show_images = self.view._config.get(
            'interface.graphview-show-images')
        self.show_ID = self.view._config.get(
            'interface.graphview-show-id')
        self.show_avatars = self.view._config.get(
            'interface.graphview-show-avatars')
        self.show_full_dates = self.view._config.get(
            'interface.graphview-show-full-dates')
        self.show_places = self.view._config.get(
            'interface.graphview-show-places')
        self.place_format = self.view._config.get(
            'interface.graphview-place-format') - 1
        self.show_tag_color = self.view._config.get(
            'interface.graphview-show-tags')
        spline = self.view._config.get('interface.graphview-show-lines')
        self.spline = SPLINE.get(int(spline))
        self.descendant_generations = self.view._config.get(
            'interface.graphview-descendant-generations')
        self.ancestor_generations = self.view._config.get(
            'interface.graphview-ancestor-generations')
        self.people_limit = self.view._config.get(
            'interface.graphview-people-limit')
        self.person_theme_index = self.view._config.get(
            'interface.graphview-person-theme')
        self.show_all_connected = self.view._config.get(
            'interface.graphview-show-all-connected')
        ranksep = self.view._config.get('interface.graphview-ranksep')
        ranksep = ranksep * 0.1
        nodesep = self.view._config.get('interface.graphview-nodesep')
        nodesep = nodesep * 0.1
        self.avatars.update_current_style()
        # get background color from gtk theme and convert it to hex
        # else use white background
        bg_color = self.context.lookup_color('theme_bg_color')
        if bg_color[0]:
            bg_rgb = (bg_color[1].red, bg_color[1].green, bg_color[1].blue)
            bg_color = rgb_to_hex(bg_rgb)
        else:
            bg_color = '#ffffff'

        # get font color from gtk theme and convert it to hex
        # else use black font
        font_color = self.context.lookup_color('theme_fg_color')
        if font_color[0]:
            fc_rgb = (font_color[1].red, font_color[1].green,
                      font_color[1].blue)
            font_color = rgb_to_hex(fc_rgb)
        else:
            font_color = '#000000'

        # get colors from config
        home_path_color = self.view._config.get(
            'interface.graphview-home-path-color')

        # set of colors
        self.colors = {'link_color':      font_color,
                       'home_path_color': home_path_color}

        self.arrowheadstyle = 'none'
        self.arrowtailstyle = 'none'

        dpi = 72
        # use font from config if needed
        font = self.view._config.get('interface.graphview-font')
        fontfamily = self.resolve_font_name(font[0])
        self.fontsize = font[1]
        if not self.bold_size:
            self.bold_size = self.norm_size = font[1]

        pagedir = "BL"
        direction = self.view._config.get('interface.graphview-direction')
        rankdir = {0: "TB", 1: "BT", 2: "LR", 3: "RL"}
        ratio = "compress"
        # as we are not using paper,
        # choose a large 'page' size with no margin
        sizew = 100
        sizeh = 100
        xmargin = 0.00
        ymargin = 0.00

        self.write('digraph GRAMPS_graph\n')
        self.write('{\n')
        self.write(' bgcolor="%s";\n' % bg_color)
        self.write(' center="false"; \n')
        self.write(' charset="utf8";\n')
        self.write(' concentrate="false";\n')
        self.write(' dpi="%d";\n' % dpi)
        self.write(' graph [fontsize=%3.1f];\n' % self.fontsize)
        self.write(' margin="%3.2f,%3.2f"; \n' % (xmargin, ymargin))
        self.write(' mclimit="99";\n')
        self.write(' nodesep="%.2f";\n' % nodesep)
        self.write(' outputorder="edgesfirst";\n')
        self.write(' pagedir="%s";\n' % pagedir)
        self.write(' rankdir="%s";\n' % rankdir.get(direction, "TB"))
        self.write(' ranksep="%.2f";\n' % ranksep)
        self.write(' ratio="%s";\n' % ratio)
        self.write(' searchsize="100";\n')
        self.write(' size="%3.2f,%3.2f"; \n' % (sizew, sizeh))
        self.write(' splines=%s;\n' % self.spline)
        self.write('\n')
        self.write(' edge [style=solid fontsize=%d];\n' % self.fontsize)

        if fontfamily:
            self.write(' node [style=filled fontname="%s" '
                       'fontsize=%3.1f fontcolor="%s"];\n'
                       % (fontfamily, self.norm_size, font_color))
        else:
            self.write(' node [style=filled fontsize=%3.1f fontcolor="%s"];\n'
                       % (self.norm_size, font_color))
        self.write('\n')
        self.uistate.connect('font-changed', self.font_changed)
        self.symbols = Symbols()
        self.font_changed()

    def resolve_font_name(self, font_name):
        """
        Helps to resolve font by graphviz.
        """
        # Sometimes graphviz have problem with font resolving.
        font_family_map = {"Times New Roman": "Times",
                           "Times Roman":     "Times",
                           "Times-Roman":     "Times",
                           }
        font = font_family_map.get(font_name)
        if font is None:
            font = font_name
        return font

    def font_changed(self):
        dth_idx = self.uistate.death_symbol
        if self.uistate.symbols:
            self.bth = self.symbols.get_symbol_for_string(
                self.symbols.SYMBOL_BIRTH)
            self.dth = self.symbols.get_death_symbol_for_char(dth_idx)
        else:
            self.bth = self.symbols.get_symbol_fallback(
                self.symbols.SYMBOL_BIRTH)
            self.dth = self.symbols.get_death_symbol_fallback(dth_idx)
        # make sure to display in selected symbols font
        self.sym_font = config.get('utf8.selected-font')
        self.bth = '<FONT FACE="%s">%s</FONT>' % (self.sym_font, self.bth)
        self.dth = '<FONT FACE="%s">%s</FONT>' % (self.sym_font, self.dth)

    def build_graph(self, active_person, path_to_home_person):
        """
        Builds a GraphViz tree based on the active person.
        """
        # reinit dot file stream (write starting graphviz dot code to file)
        self.init_dot()

        if active_person:
            self.home_person = self.dbstate.db.get_default_person()
            self.set_current_list(active_person)
            self.set_current_list_desc(active_person)
            self.path_to_home_person = True

            if path_to_home_person:
                self.person_handles_dict.update(
                    self.find_path_to_home(active_person))
            else:
                if self.show_all_connected:
                    self.person_handles_dict.update(
                        self.find_connected(active_person))
                else:
                    self.person_handles_dict.update(
                        self.find_descendants(active_person))
                    self.person_handles_dict.update(
                        self.find_ancestors(active_person))

            if self.person_handles_dict:
                self.person_handles = sorted(
                    self.person_handles_dict,
                    key=self.person_handles_dict.__getitem__,
                    reverse=True)
                self.add_persons_and_families()
                self.add_child_links_to_families()

        # close the graphviz dot code with a brace
        self.write('}\n')

        # get DOT and generate SVG data by Graphviz
        dot_data = self.dot.getvalue().encode('utf8')
        svg_data = self.make_svg(dot_data)

        return (dot_data, svg_data)

    def make_svg(self, dot_data):
        """
        Make SVG data by Graphviz.
        """
        if win():
            svg_data = Popen(['dot', '-Tsvg'],
                             creationflags=DETACHED_PROCESS,
                             stdin=PIPE,
                             stdout=PIPE,
                             stderr=PIPE).communicate(input=dot_data)[0]
        else:
            svg_data = Popen(['dot', '-Tsvg'],
                             stdin=PIPE,
                             stdout=PIPE).communicate(input=dot_data)[0]
        return svg_data

    def set_current_list(self, active_person, recurs_list=None):
        """
        Get the path from the active person to the home person.
        Select ancestors.
        """
        if not active_person:
            return False
        person = self.database.get_person_from_handle(active_person)
        if recurs_list is None:
            recurs_list = set()  # make a recursion check list (actually a set)
        # see if we have a recursion (database loop)
        elif active_person in recurs_list:
            logging.warning(_("Relationship loop detected"))
            return False
        recurs_list.add(active_person)  # record where we have been for check
        if person == self.home_person:
            self.current_list.append(active_person)
            return True
        else:
            for fam_handle in person.get_parent_family_handle_list():
                family = self.database.get_family_from_handle(fam_handle)
                if self.set_current_list(family.get_father_handle(),
                                         recurs_list=recurs_list):
                    self.current_list.append(active_person)
                    self.current_list.append(fam_handle)
                    return True
                if self.set_current_list(family.get_mother_handle(),
                                         recurs_list=recurs_list):
                    self.current_list.append(active_person)
                    self.current_list.append(fam_handle)
                    return True
        return False

    def set_current_list_desc(self, active_person, recurs_list=None):
        """
        Get the path from the active person to the home person.
        Select children.
        """
        if not active_person:
            return False
        person = self.database.get_person_from_handle(active_person)
        if recurs_list is None:
            recurs_list = set()  # make a recursion check list (actually a set)
        # see if we have a recursion (database loop)
        elif active_person in recurs_list:
            logging.warning(_("Relationship loop detected"))
            return False
        recurs_list.add(active_person)  # record where we have been for check
        if person == self.home_person:
            self.current_list.append(active_person)
            return True
        else:
            for fam_handle in person.get_family_handle_list():
                family = self.database.get_family_from_handle(fam_handle)
                for child in family.get_child_ref_list():
                    if self.set_current_list_desc(child.ref,
                                                  recurs_list=recurs_list):
                        self.current_list.append(active_person)
                        self.current_list.append(fam_handle)
                        return True
        return False

    def find_connected(self, active_person):
        """
        Spider the database from the active person.
        """
        person = self.database.get_person_from_handle(active_person)
        person_handles = {}
        self.add_connected(person, self.descendant_generations,
                           self.ancestor_generations, person_handles)
        return person_handles

    def add_connected(self, person, num_desc, num_anc, person_handles):
        """
        Include all connected to active in the list of people to graph.
        Recursive algorithm is not used becasue some trees have been found
        that exceed the standard python recursive depth.
        """
        # list of work to do, handles with generation delta,
        # add to right and pop from left
        todo = deque([(person, 0)])

        while todo:
            # check for person count
            if (self.people_limit > 0
                and len(person_handles) >= self.people_limit):
                w_msg = _("This graph would contain at least {people_count} "
                          "people, which exceeds the limit of {people_limit} "
                          "people. For performance reasons, at least "
                          "{people_missing} people won't be shown. You can "
                          "change this limit in the view configuration.".format(
                              people_count=len(todo) + len(person_handles),
                              people_limit=self.people_limit,
                              people_missing=len(todo),
                            )
                         )
                WarningDialog(_("Incomplete graph"), w_msg)
                return

            person, delta_gen = todo.popleft()

            if not person:
                continue
                
            if not self.has_family_tag(person):
                continue
            
            # check generation restrictions
            if (delta_gen > num_desc) or (delta_gen < -num_anc):
                continue

            # check if handle is not already processed
            if person.handle not in person_handles:
                spouses_list = person.get_family_handle_list()
                person_handles[person.handle] = len(spouses_list)
            else:
                continue

            # add descendants
            for family_handle in spouses_list:
                family = self.database.get_family_from_handle(family_handle)

                # add every child recursively
                if num_desc >= (delta_gen + 1):  # generation restriction
                    for child_ref in family.get_child_ref_list():
                        if (child_ref.ref in person_handles
                            or child_ref.ref in todo):
                                continue
                        todo.append(
                            (self.database.get_person_from_handle(child_ref.ref),
                             delta_gen+1))

                # add person spouses
                for sp_handle in (family.get_father_handle(),
                                  family.get_mother_handle()):
                    if sp_handle and (sp_handle not in person_handles
                                      and sp_handle not in todo):
                        todo.append(
                            (self.database.get_person_from_handle(sp_handle),
                             delta_gen))

            # add ancestors
            if -num_anc <= (delta_gen - 1):  # generation restriction
                for family_handle in person.get_parent_family_handle_list():
                    family = self.database.get_family_from_handle(family_handle)

                    # add every ancestor's spouses
                    for sp_handle in (family.get_father_handle(),
                                      family.get_mother_handle()):
                        if sp_handle and (sp_handle not in person_handles
                                          and sp_handle not in todo):
                            todo.append(
                                (self.database.get_person_from_handle(sp_handle),
                                 delta_gen-1))

    def find_descendants(self, active_person):
        """
        Spider the database from the active person.
        """
        person = self.database.get_person_from_handle(active_person)
        person_handles = {}
        self.add_descendant(person, self.descendant_generations,
                            person_handles)
        return person_handles

    def add_descendant(self, person, num_generations, person_handles):
        """
        Include a descendant in the list of people to graph.
        """
        if not person:
            return
            
        if not self.has_family_tag(person):
            return

        # check if handle is not already processed
        # and add self and spouses
        if person.handle not in person_handles:
            spouses_list = person.get_family_handle_list()

            person_handles[person.handle] = len(spouses_list)
            self.add_spouses(person, person_handles)
        else:
            return

        if num_generations <= 0:
            return

        # add every child recursively
        for family_handle in spouses_list:
            family = self.database.get_family_from_handle(family_handle)

            for child_ref in family.get_child_ref_list():
                self.add_descendant(
                    self.database.get_person_from_handle(child_ref.ref),
                    num_generations - 1, person_handles)

    def find_path_to_home(self, active_person):
        """
        Find all the people in the direct path between the active person
        and the home person.
        """
        home_person = self.dbstate.db.get_default_person()
        active_person = self.database.get_person_from_handle(active_person)
        FilterClass = GenericFilterFactory('Person')
        filter = FilterClass()
        plist = self.database.iter_person_handles()
        path = rules.person.RelationshipPathBetween([active_person.gramps_id, home_person.gramps_id])
        filter.add_rule(path)
        person_list = filter.apply(self.database, plist)
        person_handles = dict.fromkeys(person_list,0)
        return person_handles

    def add_spouses(self, person, person_handles):
        """
        Add spouses to the list.
        """
        if not person:
            return

        for family_handle in person.get_family_handle_list():
            sp_family = self.database.get_family_from_handle(family_handle)

            for sp_handle in (sp_family.get_father_handle(),
                              sp_family.get_mother_handle()):
                if sp_handle and sp_handle not in person_handles:
                    # add only spouse (num_generations = 0)
                    self.add_descendant(
                        self.database.get_person_from_handle(sp_handle),
                        0, person_handles)

    def find_ancestors(self, active_person):
        """
        Spider the database from the active person.
        """
        person = self.database.get_person_from_handle(active_person)
        person_handles = {}
        self.add_ancestor(person, self.ancestor_generations, person_handles)
        return person_handles

    def add_ancestor(self, person, num_generations, person_handles):
        """
        Include an ancestor in the list of people to graph.
        """
        if not person:
            return

        # Apply the ProfileTag filter to ancestors too.
        # Parent-family traversal includes foster and adoptive parents, so
        # untagged parents must be rejected just like descendants and spouses.
        if not self.has_family_tag(person):
            return

        # add self if handle is not already processed
        if person.handle not in person_handles:
            person_handles[person.handle] = len(person.get_family_handle_list())
        else:
            return

        if num_generations <= 0:
            return

        for family_handle in person.get_parent_family_handle_list():
            family = self.database.get_family_from_handle(family_handle)

            # add parents
            sp_persons = []
            for sp_handle in (family.get_father_handle(),
                              family.get_mother_handle()):
                if sp_handle and sp_handle not in person_handles:
                    sp_person = self.database.get_person_from_handle(sp_handle)
                    self.add_ancestor(sp_person,
                                      num_generations - 1,
                                      person_handles)
                    sp_persons.append(sp_person)

            # add every other spouses for parents
            for sp_person in sp_persons:
                self.add_spouses(sp_person, person_handles)

    def add_child_links_to_families(self):
        """
        Returns string of GraphViz edges linking parents to families or
        children.
        """
        for person_handle in self.person_handles:
            person = self.database.get_person_from_handle(person_handle)
            for fam_handle in person.get_parent_family_handle_list():
                family = self.database.get_family_from_handle(fam_handle)
                father_handle = family.get_father_handle()
                mother_handle = family.get_mother_handle()
                for child_ref in family.get_child_ref_list():
                    if child_ref.ref == person_handle:
                        frel = child_ref.frel
                        mrel = child_ref.mrel
                        break
                if((father_handle in self.person_handles) or
                   (mother_handle in self.person_handles)):
                    # link to the family node if either parent is in graph
                    self.add_family_link(person_handle, family, frel, mrel)

    def add_family_link(self, p_id, family, frel, mrel):
        """
        Links the child to a family.
        """
        style = 'solid'
        adopted = ((int(frel) != ChildRefType.BIRTH) or
                   (int(mrel) != ChildRefType.BIRTH))
        # if birth relation to father is NONE, meaning there is no father and
        # if birth relation to mother is BIRTH then solid line
        if((int(frel) == ChildRefType.NONE) and
           (int(mrel) == ChildRefType.BIRTH)):
            adopted = False
        if adopted:
            style = 'dotted'
        self.add_link(family.handle, p_id, style,
                      self.arrowheadstyle, self.arrowtailstyle,
                      color=self.colors['home_path_color'],
                      bold=self.is_in_path_to_home(p_id))

    def add_parent_link(self, p_id, parent_handle, rel):
        """
        Links the child to a parent.
        """
        style = 'solid'
        if int(rel) != ChildRefType.BIRTH:
            style = 'dotted'
        self.add_link(parent_handle, p_id, style,
                      self.arrowheadstyle, self.arrowtailstyle,
                      color=self.colors['home_path_color'],
                      bold=self.is_in_path_to_home(p_id))

    def add_persons_and_families(self):
        """
        Adds nodes for persons and their families.
        Subgraphs are used to indicate to Graphviz that parents of families
        should be positioned together. The person_handles list is sorted so
        that people with the largest number of spouses are at the start of the
        list. As families are only processed once, this means people with
        multiple spouses will have their additional spouses included in their
        subgraph.
        """
        # variable to communicate with get_person_label
        url = ""

        # The list of families for which we have output the node,
        # so we don't do it twice
        # use set() as it little faster then list()
        family_nodes_done = set()
        family_links_done = set()
        for person_handle in self.person_handles:
            person = self.database.get_person_from_handle(person_handle)
            # Output the person's node
            label = self.get_person_label(person)
            (shape, style, color, fill) = self.get_gender_style(person)
            self.add_node(person_handle, label, shape, color, style, fill, url)

            # Output family nodes where person is a parent
            family_list = person.get_family_handle_list()
            for fam_handle in family_list:
                if fam_handle not in family_nodes_done:
                    family_nodes_done.add(fam_handle)
                    self.__add_family_node(fam_handle)

            # Output family links where person is a parent
            subgraph_started = False
            family_list = person.get_family_handle_list()
            for fam_handle in family_list:
                if fam_handle not in family_links_done:
                    family_links_done.add(fam_handle)
                    if not subgraph_started:
                        subgraph_started = True
                        self.start_subgraph(person_handle)
                    self.__add_family_links(fam_handle)
            if subgraph_started:
                self.end_subgraph()

    def is_in_path_to_home(self, f_handle):
        """
        Is the current person in the path to the home person?
        """
        if f_handle in self.current_list:
            return True
        return False

    def __add_family_node(self, fam_handle):
        """
        Add a node for a family.
        """
        fam = self.database.get_family_from_handle(fam_handle)
        fill, color = color_graph_family(fam, self.dbstate)
        style = "filled"
        label = self.get_family_label(fam)

        self.add_node(fam_handle, label, "ellipse", color, style, fill)

    def __add_family_links(self, fam_handle):
        """
        Add the links for spouses.
        """
        fam = self.database.get_family_from_handle(fam_handle)
        f_handle = fam.get_father_handle()
        m_handle = fam.get_mother_handle()
        if f_handle in self.person_handles:
            self.add_link(f_handle,
                          fam_handle, "",
                          self.arrowheadstyle,
                          self.arrowtailstyle,
                          color=self.colors['home_path_color'],
                          bold=self.is_in_path_to_home(f_handle))
        if m_handle in self.person_handles:
            self.add_link(m_handle,
                          fam_handle, "",
                          self.arrowheadstyle,
                          self.arrowtailstyle,
                          color=self.colors['home_path_color'],
                          bold=self.is_in_path_to_home(m_handle))

    def get_gender_style(self, person):
        """
        Return gender specific person style.
        """
        gender = person.get_gender()
        shape = "box"
        style = "solid, filled"

        # get alive status of person to get box color
        try:
            alive = probably_alive(person, self.dbstate.db)
        except RuntimeError:
            alive = False

        fill, color = color_graph_box(alive, gender)
        return(shape, style, color, fill)

    def get_tags_and_table(self, obj):
        """
        Return html tags table for obj (person or family).
        """
        tag_table = ''
        tags = []

        for tag_handle in obj.get_tag_list():
            tags.append(self.dbstate.db.get_tag_from_handle(tag_handle))

        # prepare html table of tags
        if tags:
            tag_table = ('<TABLE BORDER="0" CELLBORDER="0" '
                         'CELLPADDING="5"><TR>')
            for tag in tags:
                rgba = Gdk.RGBA()
                rgba.parse(tag.get_color())
                value = '#%02x%02x%02x' % (int(rgba.red * 255),
                                           int(rgba.green * 255),
                                           int(rgba.blue * 255))
                tag_table += '<TD BGCOLOR="%s"></TD>' % value
            tag_table += '</TR></TABLE>'

        return tags, tag_table

    def get_person_themes(self, index=-1):
        """
        Person themes.
        If index == -1 return list of themes.
        If index out of range return default theme.
        """
        person_themes = [
            (0, _('Default'),
             '<TABLE '
             'BORDER="0" CELLSPACING="2" CELLPADDING="0" CELLBORDER="0">'
             '<TR><TD>%(img)s</TD></TR>'
             '<TR><TD><FONT POINT-SIZE="%(bsize)3.1f"><B>%(name)s</B>'
             '</FONT></TD></TR>'
             '<TR><TD ALIGN="LEFT">%(birth_str)s</TD></TR>'
             '<TR><TD ALIGN="LEFT">%(death_str)s</TD></TR>'
             '<TR><TD>%(tags)s</TD></TR>'
             '</TABLE>'
             ),
            (1, _('Image on right side'),
             '<TABLE '
             'BORDER="0" CELLSPACING="5" CELLPADDING="0" CELLBORDER="0">'
             '<tr>'
             '<td colspan="2"><FONT POINT-SIZE="%(bsize)3.1f"><B>%(name)s'
             '</B></FONT></td>'
             '</tr>'
             '<tr>'
             '<td ALIGN="LEFT" BALIGN="LEFT" CELLPADDING="5">%(birth_wraped)s'
             '</td>'
             '<td rowspan="2">%(img)s</td>'
             '</tr>'
             '<tr>'
             '<td ALIGN="LEFT" BALIGN="LEFT" CELLPADDING="5">%(death_wraped)s'
             '</td>'
             '</tr>'
             '<tr>'
             '  <td colspan="2">%(tags)s</td>'
             '</tr>'
             '</TABLE>'
             ),
            (2, _('Image on left side'),
             '<TABLE '
             'BORDER="0" CELLSPACING="5" CELLPADDING="0" CELLBORDER="0">'
             '<tr>'
             '<td colspan="2"><FONT POINT-SIZE="%(bsize)3.1f"><B>%(name)s'
             '</B></FONT></td>'
             '</tr>'
             '<tr>'
             '<td rowspan="2">%(img)s</td>'
             '<td ALIGN="LEFT" BALIGN="LEFT" CELLPADDING="5">%(birth_wraped)s'
             '</td>'
             '</tr>'
             '<tr>'
             '<td ALIGN="LEFT" BALIGN="LEFT" CELLPADDING="5">%(death_wraped)s'
             '</td>'
             '</tr>'
             '<tr>'
             '  <td colspan="2">%(tags)s</td>'
             '</tr>'
             '</TABLE>'
             ),
            (3, _('Normal'),
             '<TABLE '
             'BORDER="0" CELLSPACING="2" CELLPADDING="0" CELLBORDER="0">'
             '<TR><TD>%(img)s</TD></TR>'
             '<TR><TD><FONT POINT-SIZE="%(bsize)3.1f"><B>%(name)s'
             '</B></FONT></TD></TR>'
             '<TR><TD ALIGN="LEFT" BALIGN="LEFT">%(birth_wraped)s</TD></TR>'
             '<TR><TD ALIGN="LEFT" BALIGN="LEFT">%(death_wraped)s</TD></TR>'
             '<TR><TD>%(tags)s</TD></TR>'
             '</TABLE>'
             )]

        if index < 0:
            return person_themes

        if index < len(person_themes):
            return person_themes[index]
        else:
            return person_themes[0]

    def get_person_label(self, person):
        """
        Return person label string (with tags).
        """
        # Start an HTML table.
        # Remember to close the table afterwards!
        #
        # This isn't a free-form HTML format here...just a few keywords that
        # happen to be similar to keywords commonly seen in HTML.
        # For additional information on what is allowed, see:
        #
        #       http://www.graphviz.org/info/shapes.html#html
        #
        # Will use html.escape to avoid '&', '<', '>' in the strings.

        # FIRST get all strings: img, name, dates, tags

        # see if we have an image to use for this person
        image = ''
        if self.show_images:
            image = self.view.graph_widget.get_person_image(person,
                                                            kind='path')
            if not image and self.show_avatars:
                image = self.avatars.get_avatar(gender=person.gender)

            if image is not None:
                image = '<IMG SRC="%s"/>' % image
            else:
                image = ''

        # get the person's name
        name = displayer.display_name(person.get_primary_name())
        # name string should not be empty
        name = escape(name) if name else ' '
        if self.show_ID:
            name += " (%s)" % person.get_gramps_id()

        # birth, death is a lists [date, place]
        birth, death = self.get_date_strings(person)

        birth_str = ''
        death_str = ''
        birth_wraped = ''
        death_wraped = ''

        # There are two ways of displaying dates:
        # 1) full and on two lines:
        #       b. 1890-12-31 - BirthPlace
        #       d. 1960-01-02 - DeathPlace
        if self.show_full_dates or self.show_places:
            # add symbols
            if birth[0]:
                birth[0] = '%s %s' % (self.bth, birth[0])
                birth_wraped = birth[0]
                birth_str = birth[0]
                if birth[1]:
                    birth_wraped += '<BR/>'
                    birth_str += '  '
            elif birth[1]:
                birth_wraped = _('%s ') % self.bth
                birth_str = _('%s ') % self.bth
            birth_wraped += birth[1]
            birth_str += birth[1]

            if death[0]:
                death[0] = '%s %s' % (self.dth, death[0])
                death_wraped = death[0]
                death_str = death[0]
                if death[1]:
                    death_wraped += '<BR/>'
                    death_str += '  '
            elif death[1]:
                death_wraped = _('%s ') % self.dth
                death_str = _('%s ') % self.dth
            death_wraped += death[1]
            death_str += death[1]

        # 2) simple and on one line:
        #       (1890 - 1960)
        else:
            if birth[0] or death[0]:
                birth_str = '(%s - %s)' % (birth[0], death[0])
                # add symbols
                if image:
                    if birth[0]:
                        birth_wraped = '%s %s' % (self.bth, birth[0])
                    if death[0]:
                        death_wraped = '%s %s' % (self.dth, death[0])
                else:
                    birth_wraped = birth_str

        # get tags table for person and add tooltip for node
        tag_table = ''
        if self.show_tag_color:
            tags, tag_table = self.get_tags_and_table(person)
            if tag_table:
                self.add_tags_tooltip(person.handle, tags)

        # apply theme to person label
        if(image or self.person_theme_index == 0 or
           self.person_theme_index == 3):
            p_theme = self.get_person_themes(self.person_theme_index)
        else:
            # use default theme if no image
            p_theme = self.get_person_themes(3)

        label = p_theme[2] % {'img': image,
                              'name': name,
                              'birth_str': birth_str,
                              'death_str': death_str,
                              'birth_wraped': birth_wraped,
                              'death_wraped': death_wraped,
                              'tags': tag_table,
                              'bsize' : self.bold_size}
        return label

    def get_family_label(self, family):
        """
        Return family label string (with tags).
        """
        # start main html table
        label = ('<TABLE '
                 'BORDER="0" CELLSPACING="2" CELLPADDING="0" CELLBORDER="0">')

        # add dates strtings to table
        event_str = ['', '']
        for event_ref in family.get_event_ref_list():
            event = self.database.get_event_from_handle(event_ref.ref)
            if (event.type == EventType.MARRIAGE and
                    (event_ref.get_role() == EventRoleType.FAMILY or
                     event_ref.get_role() == EventRoleType.PRIMARY)):
                event_str = self.get_event_string(event)
                break
        if event_str[0] and event_str[1]:
            event_str = '%s<BR/>%s' % (event_str[0], event_str[1])
        elif event_str[0]:
            event_str = event_str[0]
        elif event_str[1]:
            event_str = event_str[1]
        else:
            event_str = ''

        label += '<TR><TD>%s</TD></TR>' % event_str

        # add tags table for family and add tooltip for node
        if self.show_tag_color:
            tags, tag_table = self.get_tags_and_table(family)

            if tag_table:
                label += '<TR><TD>%s</TD></TR>' % tag_table
                self.add_tags_tooltip(family.handle, tags)

        # close main table
        label += '</TABLE>'

        return label

    def get_date_strings(self, person):
        """
        Returns tuple of birth/christening and death/burying date strings.
        """
        birth_event = get_birth_or_fallback(self.database, person)
        if birth_event:
            birth = self.get_event_string(birth_event)
        else:
            birth = ['', '']

        death_event = get_death_or_fallback(self.database, person)
        if death_event:
            death = self.get_event_string(death_event)
        else:
            death = ['', '']

        return (birth, death)

    def get_event_string(self, event):
        """
        Return string for an event label.

        Based on the data availability and preferences, we select one
        of the following for a given event:
            year only
            complete date
            place name
            empty string
        """
        if event:
            place_title = place_displayer.display_event(self.database, event,
                                                        fmt=self.place_format)
            date_object = event.get_date_object()
            date = ''
            place = ''
            # shall we display full date
            # or do we have a valid year to display only year
            if(self.show_full_dates and date_object.get_text() or
               date_object.get_year_valid()):
                if self.show_full_dates:
                    date = '%s' % datehandler.get_date(event)
                else:
                    date = '%i' % date_object.get_year()
                # shall we add the place?
                if self.show_places and place_title:
                    place = place_title
                return [escape(date), escape(place)]
            else:
                if place_title and self.show_places:
                    return ['', escape(place_title)]
        return ['', '']

    def add_link(self, id1, id2, style="", head="", tail="", comment="",
                 bold=False, color=""):
        """
        Add a link between two nodes.
        Gramps handles are used as nodes but need to be prefixed
        with an underscore because Graphviz does not like IDs
        that begin with a number. The id is quoted because handles are
        arbitrary schema-valid strings: Gramps-Web creates UUIDv4 handles
        containing hyphens, which an unquoted Graphviz ID would split on
        (bug 13832).
        """
        self.write('  "_%s" -> "_%s"' % (id1, id2))

        boldok = False
        if id1 in self.current_list:
            if id2 in self.current_list:
                boldok = True

        self.write(' [')

        if style:
            self.write(' style=%s' % style)
        if head:
            self.write(' arrowhead=%s' % head)
        if tail:
            self.write(' arrowtail=%s' % tail)
        if bold and boldok:
            self.write(' penwidth=%d' % 5)
            if color:
                self.write(' color="%s"' % color)
        else:
            # if not path to home than set default color of link
            self.write(' color="%s"' % self.colors['link_color'])

        self.write(' ]')

        self.write(';')

        if comment:
            self.write(' // %s' % comment)

        self.write('\n')

    def add_node(self, node_id, label, shape="", color="",
                 style="", fillcolor="", url="", fontsize=""):
        """
        Add a node to this graph.
        Nodes can be different shapes like boxes and circles.
        Gramps handles are used as nodes but need to be prefixed with an
        underscore because Graphviz does not like IDs that begin with a number.
        """
        text = '[margin="0.11,0.08"'

        if shape:
            text += ' shape="%s"' % shape

        if color:
            text += ' color="%s"' % color

        if fillcolor:
            color = hex_to_rgb_float(fillcolor)
            yiq = (color[0] * 299 + color[1] * 587 + color[2] * 114)
            fontcolor = "#ffffff" if yiq < 500 else "#000000"
            text += ' fillcolor="%s" fontcolor="%s"' % (fillcolor, fontcolor)
        if style:
            text += ' style="%s"' % style

        if fontsize:
            text += ' fontsize="%s"' % fontsize
        # note that we always output a label -- even if an empty string --
        # otherwise GraphViz uses the node ID as the label which is unlikely
        # to be what the user wants to see in the graph
        text += ' label=<%s>' % label

        if url:
            text += ' URL="%s"' % url

        text += " ]"
        # Quote the id: handles are arbitrary schema-valid strings, and
        # Gramps-Web creates UUIDv4 handles with hyphens that an unquoted
        # Graphviz ID would split on, blanking the graph (bug 13832).
        self.write(' "_%s" %s;\n' % (node_id, text))

    def add_tags_tooltip(self, handle, tag_list):
        """
        Add tooltip to dict {handle, tooltip}.
        """
        tooltip_str = _('<b>Tags:</b>')
        for tag in tag_list:
            tooltip_str += ('\n<span background="%s">  </span> - %s'
                            % (tag.get_color(), tag.get_name()))
        self.view.tags_tooltips[handle] = tooltip_str

    def start_subgraph(self, graph_id):
        """
        Opens a subgraph which is used to keep together related nodes
        on the graph.
        """
        # Quote the name: graph_id is a handle (see bug 13832); a UUIDv4
        # handle with hyphens would break an unquoted subgraph name.
        # Graphviz still treats a quoted name beginning with "cluster" as
        # a cluster subgraph.
        self.write('\n subgraph "cluster_%s"\n' % graph_id)
        self.write(' {\n')
        # no border around subgraph (#0002176)
        self.write('  style="invis";\n')

    def end_subgraph(self):
        """
        Closes a subgraph section.
        """
        self.write(' }\n\n')

    def write(self, text):
        """
        Write text to the dot file.
        """
        if self.dot:
            self.dot.write(text)


#-------------------------------------------------------------------------
#
# CanvasAnimation
#
#-------------------------------------------------------------------------
class CanvasAnimation(object):
    """
    Produce animation for operations with canvas.
    """
    def __init__(self, view, canvas, scroll_window):
        """
        We need canvas and window in which it placed.
        And view to get config.
        """
        self.view = view
        self.canvas = canvas
        self.hadjustment = scroll_window.get_hadjustment()
        self.vadjustment = scroll_window.get_vadjustment()
        self.items_list = []
        self.in_motion = False
        self.max_count = self.view._config.get(
            'interface.graphview-animation-count')
        self.max_count = self.max_count * 2  # must be modulo 2

        self.show_animation = self.view._config.get(
            'interface.graphview-show-animation')

        # delay between steps in microseconds
        self.speed = self.view._config.get(
            'interface.graphview-animation-speed')
        self.speed = 50 * int(self.speed)
        # length of step
        self.step_len = 10

        # separated counter and direction of shaking
        # for each item that in shake procedure
        self.counter = {}
        self.shake = {}
        self.in_shake = []

    def update_items(self, items_list):
        """
        Update list of items for current graph.
        """
        self.items_list.clear()
        self.items_list.extend(items_list)

        self.in_shake.clear()
        # clear counters and shakes - items not exists anymore
        self.counter.clear()
        self.shake.clear()

    def stop_animation(self):
        """
        Stop move_to animation.
        And wait while thread is finished.
        """
        self.in_motion = False
        try:
            self.thread.join()
        except:
            pass

    def stop_shake_animation(self, item, stoped):
        """
        Processing of 'animation-finished' signal.
        Stop or keep shaking item depending on counter for item.
        """
        counter = self.counter.get(item.title)
        shake = self.shake.get(item.title)

        if (not stoped) and counter and shake and counter < self.max_count:
            self.shake[item.title] = (-1) * self.shake[item.title]
            self.counter[item.title] += 1
            item.animate(0, self.shake[item.title], 1, 0, False,
                         self.speed, 10, 0)
        else:
            item.disconnect_by_func(self.stop_shake_animation)
            try:
                self.counter.pop(item.title)
                self.shake.pop(item.title)
            except:
                pass

    def shake_person(self, person_handle):
        """
        Shake person node to help to see it.
        Use build-in function of CanvasItem.
        """
        item = self.get_item_by_title(person_handle)
        if item:
            self.shake_item(item)

    def shake_item(self, item):
        """
        Shake item to help to see it.
        Use build-in function of CanvasItem.
        """
        if item and self.show_animation and self.max_count > 0:
            if not self.counter.get(item.title):
                self.in_shake.append(item)
                self.counter[item.title] = 1
                self.shake[item.title] = 10
                item.connect('animation-finished', self.stop_shake_animation)
                item.animate(0, self.shake[item.title], 1, 0, False,
                             self.speed, 10, 0)

    def get_item_by_title(self, handle):
        """
        Find item by title.
        """
        if handle:
            for item in self.items_list:
                if item.title == handle:
                    return item
        return None

    def move_to_person(self, handle, animated):
        """
        Move graph to specified person by handle.
        """
        self.stop_animation()
        item = self.get_item_by_title(handle)
        if item:
            bounds = item.get_bounds()
            # calculate middle of node coordinates
            xxx = (bounds.x2 - (bounds.x2 - bounds.x1) / 2)
            yyy = (bounds.y1 - (bounds.y1 - bounds.y2) / 2)
            self.move_to(item, (xxx, yyy), animated)
            return True
        return False

    def get_trace_to(self, destination):
        """
        Return next point to destination from current position.
        """
        # get current position (left-top corner) with scale
        start_x = self.hadjustment.get_value() / self.canvas.get_scale()
        start_y = self.vadjustment.get_value() / self.canvas.get_scale()

        x_delta = destination[0] - start_x
        y_delta = destination[1] - start_y

        # calculate step count depending on length of the trace
        trace_len = sqrt(pow(x_delta, 2) + pow(y_delta, 2))
        steps_count = int(trace_len / self.step_len * self.canvas.get_scale())

        # prevent division by 0
        if steps_count > 0:
            x_step = x_delta / steps_count
            y_step = y_delta / steps_count

            point = (start_x + x_step, start_y + y_step)
        else:
            point = destination
        return point

    def scroll_canvas(self, point):
        """
        Scroll window to point on canvas.
        """
        self.canvas.scroll_to(point[0], point[1])

    def animation(self, item, destination):
        """
        Animate scrolling to destination point in thread.
        Dynamically get points to destination one by one
        and try to scroll to them.
        """
        self.in_motion = True
        while self.in_motion:
            # correct destination to window centre
            h_offset = self.hadjustment.get_page_size() / 2
            v_offset = self.vadjustment.get_page_size() / 3
            # apply the scaling factor so the offset is adjusted to the scale
            h_offset = h_offset / self.canvas.get_scale()
            v_offset = v_offset / self.canvas.get_scale()

            dest = (destination[0] - h_offset,
                    destination[1] - v_offset)

            # get maximum scroll of window
            max_scroll_x = ((self.hadjustment.get_upper() -
                             self.hadjustment.get_page_size()) /
                            self.canvas.get_scale())
            max_scroll_y = ((self.vadjustment.get_upper() -
                             self.vadjustment.get_page_size()) /
                            self.canvas.get_scale())

            # fix destination to fit in max scroll
            if dest[0] > max_scroll_x:
                dest = (max_scroll_x, dest[1])
            if dest[0] < 0:
                dest = (0, dest[1])
            if dest[1] > max_scroll_y:
                dest = (dest[0], max_scroll_y)
            if dest[1] < 0:
                dest = (dest[0], 0)

            cur_pos = (self.hadjustment.get_value() / self.canvas.get_scale(),
                       self.vadjustment.get_value() / self.canvas.get_scale())

            # finish if we already at destination
            if dest == cur_pos:
                break

            # get next point to destination
            point = self.get_trace_to(dest)

            GLib.idle_add(self.scroll_canvas, point)
            GLib.usleep(20 * self.speed)

            # finish if we try to goto destination point
            if point == dest:
                break

        self.in_motion = False
        # shake item after scroll to it
        self.shake_item(item)

    def move_to(self, item, destination, animated):
        """
        Move graph to specified position.
        If 'animated' is True then movement will be animated.
        It works with 'canvas.scroll_to' in thread.
        """
        # if animated is True than run thread with animation
        # else - just scroll_to immediately
        if animated and self.show_animation:
            self.thread = Thread(target=self.animation,
                                 args=[item, destination])
            self.thread.start()
        else:
            # correct destination to screen centre
            h_offset = self.hadjustment.get_page_size() / 2
            v_offset = self.vadjustment.get_page_size() / 3

            # apply the scaling factor so the offset is adjusted to the scale
            h_offset = h_offset / self.canvas.get_scale()
            v_offset = v_offset / self.canvas.get_scale()

            destination = (destination[0] - h_offset,
                           destination[1] - v_offset)
            self.scroll_canvas(destination)
            # shake item after scroll to it
            self.shake_item(item)


#-------------------------------------------------------------------------
#
# Popup menu widget
#
#-------------------------------------------------------------------------
class PopupMenu(Gtk.Menu):
    """
    Produce popup widget for right-click menu.
    """
    def __init__(self, graph_widget, kind=None, handle=None):
        """
        graph_widget: GraphWidget
        kind: 'person', 'family', 'background'
        handle: person or family handle
        """
        Gtk.Menu.__init__(self)
        self.set_reserve_toggle_size(False)

        self.graph_widget = graph_widget
        self.view = graph_widget.view
        self.dbstate = graph_widget.dbstate

        self.actions = graph_widget.actions

        if kind == 'background':
            self.background_menu()
        elif kind == 'person' and handle is not None:
            self.person_menu(handle)
        elif kind == 'family' and handle is not None:
            self.family_menu(handle)

    def show_menu(self, event=None):
        """
        Show popup menu.
        """
        if (Gtk.MAJOR_VERSION >= 3) and (Gtk.MINOR_VERSION >= 22):
            # new from gtk 3.22:
            self.popup_at_pointer(event)
        else:
            if event:
                self.popup(None, None, None, None,
                           event.get_button()[1], event.time)
            else:
                self.popup(None, None, None, None,
                           0, Gtk.get_current_event_time())
                #self.popup(None, None, None, None, 0, 0)

    def background_menu(self):
        """
        Popup menu on background.
        """        
        menu_item = Gtk.CheckMenuItem(_('Show images'))
        menu_item.set_active(
            self.view._config.get('interface.graphview-show-images'))
        menu_item.connect("activate", self.graph_widget.update_setting,
                          'interface.graphview-show-images')
        menu_item.show()
        self.append(menu_item)

        menu_item = Gtk.CheckMenuItem(_('Highlight the home person'))
        menu_item.set_active(
            self.view._config.get('interface.graphview-highlight-home-person'))
        menu_item.connect("activate", self.graph_widget.update_setting,
                          'interface.graphview-highlight-home-person')
        menu_item.show()
        self.append(menu_item)

        menu_item = Gtk.CheckMenuItem(_('Show full dates'))
        menu_item.set_active(
            self.view._config.get('interface.graphview-show-full-dates'))
        menu_item.connect("activate", self.graph_widget.update_setting,
                          'interface.graphview-show-full-dates')
        menu_item.show()
        self.append(menu_item)

        menu_item = Gtk.CheckMenuItem(_('Show places'))
        menu_item.set_active(
            self.view._config.get('interface.graphview-show-places'))
        menu_item.connect("activate", self.graph_widget.update_setting,
                          'interface.graphview-show-places')
        menu_item.show()
        self.append(menu_item)

        menu_item = Gtk.CheckMenuItem(_('Show tags'))
        menu_item.set_active(
            self.view._config.get('interface.graphview-show-tags'))
        menu_item.connect("activate", self.graph_widget.update_setting,
                          'interface.graphview-show-tags')
        menu_item.show()
        self.append(menu_item)

        self.add_separator()

        menu_item = Gtk.CheckMenuItem(_('Show animation'))
        menu_item.set_active(
            self.view._config.get('interface.graphview-show-animation'))
        menu_item.connect("activate", self.graph_widget.update_setting,
                          'interface.graphview-show-animation')
        menu_item.show()
        self.append(menu_item)

        menu_item = Gtk.CheckMenuItem(
            _('Show people with the person tag "ProfileTag"'))
        menu_item.set_active(
            self.view._config.get('interface.graphview-filter-family-tag'))
        menu_item.connect("activate", self.graph_widget.update_setting,
                          'interface.graphview-filter-family-tag')
        menu_item.show()
        self.append(menu_item)

        # add sub menu for line type setting
        menu_item, sub_menu = self.add_submenu(label=_('Lines type'))

        spline = self.view._config.get('interface.graphview-show-lines')

        entry = Gtk.RadioMenuItem(label=_('Direct'))
        entry.connect("activate", self.graph_widget.update_lines_type,
                      0, 'interface.graphview-show-lines')
        if spline == 0:
            entry.set_active(True)
        entry.show()
        sub_menu.append(entry)

        entry = Gtk.RadioMenuItem(label=_('Curves'))
        entry.connect("activate", self.graph_widget.update_lines_type,
                      1, 'interface.graphview-show-lines')
        if spline == 1:
            entry.set_active(True)
        entry.show()
        sub_menu.append(entry)

        entry = Gtk.RadioMenuItem(label=_('Ortho'))
        entry.connect("activate", self.graph_widget.update_lines_type,
                      2, 'interface.graphview-show-lines')
        if spline == 2:
            entry.set_active(True)
        entry.show()
        sub_menu.append(entry)

        # add profile export/import shortcuts
        self.add_separator()
        _item, profile_menu = self.add_submenu(label=_('Profiles'))
        profiles_enabled = self.view.profile_function_is_enabled()
        try:
            _item.set_sensitive(profiles_enabled)
        except Exception:
            pass
        has_current_view_profile = bool(
            self.view.current_view_profile_filename)

        # Group the popup actions under short, non-clickable
        # headings. The profile type no longer needs to be repeated in every
        # action label.
        view_heading = Gtk.MenuItem()
        view_heading_label = Gtk.Label(xalign=0)
        view_heading_label.set_markup(
            '<b>%s</b>' % escape(_('View profile:')))
        view_heading.add(view_heading_label)
        view_heading.set_sensitive(False)
        view_heading.show_all()
        profile_menu.append(view_heading)

        # Do not offer "Save current View profile" here.
        # That action follows the selections in the Profiles page, and those
        # selections are intentionally not updated by changes made elsewhere.
        # The popup offers a complete new View-profile snapshot.
        # The popup menu is normally used while the Profiles
        # page and its checkboxes are not visible. Save the complete current
        # view as a new View profile, exactly like the matching Configure
        # button, without the empty-checkbox warning.
        save_view_as_item = self.add_menuitem(
            profile_menu, _('Save as new...'),
            self.view.save_current_view_as_new_view_profile)
        save_view_as_item.set_sensitive(profiles_enabled)
        load_view_item = self.add_menuitem(
            profile_menu, _('Load...'), self.view.load_graphview_profile)
        load_view_item.set_sensitive(profiles_enabled)
        delete_view_item = self.add_menuitem(
            profile_menu, _('Delete'), self.view.delete_current_view_profile)
        delete_view_item.set_sensitive(
            profiles_enabled and has_current_view_profile)

        sep = Gtk.SeparatorMenuItem()
        sep.show()
        profile_menu.append(sep)

        standard_heading = Gtk.MenuItem()
        standard_heading_label = Gtk.Label(xalign=0)
        standard_heading_label.set_markup(
            '<b>%s</b>' % escape(_('Standard profile:')))
        standard_heading.add(standard_heading_label)
        standard_heading.set_sensitive(False)
        standard_heading.show_all()
        profile_menu.append(standard_heading)

        # The popup menu is normally used while the Profiles
        # page and its checkboxes are not visible. Save the complete current
        # view as a Standard profile, exactly like the matching Configure
        # button. Only the shared Active/Home safety check applies.
        save_standard_item = self.add_menuitem(
            profile_menu, _('Save as'),
            self.view.save_current_view_as_standard_profile)
        save_standard_item.set_sensitive(profiles_enabled)
        load_standard_item = self.add_menuitem(
            profile_menu, _('Load'), self.view.load_standard_graphview_profile)
        # Do not offer a load action when this family tree has
        # no saved Standard profile. The loader repeats the file check in
        # case the file disappears while this menu is open.
        load_standard_item.set_sensitive(
            profiles_enabled and self.view.standard_graphview_profile_exists())
        delete_standard_item = self.add_menuitem(
            profile_menu, _('Delete'),
            self.view.delete_standard_graphview_profile)
        delete_standard_item.set_sensitive(
            profiles_enabled and self.view.standard_graphview_profile_exists())

        # add help menu
        self.add_separator()
        self.append_help_menu_entry()

    def add_tags_to_menu(self, obj, otype, tag_menu):
        """
        Add tags to the Popup menu for person or family node.
        """
        idx = 0
        tags_list = obj.get_tag_list()
        handle = obj.get_handle()
        for tag_handle in self.dbstate.db.get_tag_handles():
            idx += 1
            tag = self.dbstate.db.get_tag_from_handle(tag_handle)
            # prepare the tag
            if tag:
                rgba = Gdk.RGBA()
                rgba.parse(tag.get_color())
                rgba2 = Gdk.RGBA()
                # Calculate the brightness of the background.
                # depending on this value, the text is shown
                # either in white, either in black.
                brightness = (int(rgba.red * 255) * 0.299 +
                              int(rgba.green * 255) * 0.587 +
                              int(rgba.blue * 255) * 0.114)
                foreground = "#000" if brightness > 100 else "#fff"
                rgba2.parse(foreground)
                # We can't use add_menuitem here
                tag_name = tag.get_name()
                item = Gtk.RadioMenuItem(label=tag_name)
                if tag_handle in tags_list:
                    item.set_active(True)
                else:
                    item.set_active(False)
                item.override_background_color(Gtk.StateFlags.NORMAL, rgba)
                item.override_color(Gtk.StateFlags.NORMAL, rgba2)
                item.connect("activate", self.actions.add_tag_to_object,
                             [handle, otype, tag_handle])
                item.show()
                style = tag_menu.get_style_context()
                color = style.get_property("background-color",
                                           Gtk.StateFlags.PRELIGHT)
                color.alpha = 0.2
                item.override_background_color(Gtk.StateFlags.PRELIGHT,
                                               color)
                tag_menu.append(item)

    def person_menu(self, handle):
        """
        Popup menu for person node.
        """
        person = self.dbstate.db.get_person_from_handle(handle)
        if person:
            add_menuitem(self, _('Edit'),
                         handle, self.actions.edit_person)

            add_menuitem(self, _('Copy'),
                         handle, self.actions.copy_person_to_clipboard)

            add_menuitem(self, _('Delete'),
                         person, self.actions.remove_person)

            self.add_separator()

            # build events submenu
            if len(person.get_event_ref_list()) != 0:
                iteme, evt_menu = self.add_submenu(label=_("Events"))
            else:
                iteme = self.add_menuitem(self, _("No Events for this person"), self.menu_no_action)

            nbe = 0
            for event_ref in person.get_event_ref_list():
                if not event_ref:
                    continue
                nbe += 1
                event = self.dbstate.db.get_event_from_handle(event_ref.ref)
                role = _(event_ref.get_role().xml_str())
                etype = _(event.get_type().xml_str())

                # text = displayer.display(person)
                if event_ref.get_role() != EventRoleType.PRIMARY:
                    etype += " (" + role + ") "
                self.add_menuitem(evt_menu, etype,
                                  self.actions.edit_person_event,
                                  person.get_gramps_id(), event, event_ref)

            # build tag submenu
            item, tag_menu = self.add_submenu(label=_("Tags"))

            add_menuitem(tag_menu, _('Select tags for person'),
                         [handle, 'person'], self.actions.edit_tag_list)

            add_menuitem(tag_menu, _('Organize Tags...'),
                         [handle, 'person'], self.actions.organize_tags)

            self.add_tags_to_menu(person, 'person', tag_menu)

            # go over spouses and build their menu
            item, sp_menu = self.add_submenu(label=_("Spouses"))

            add_menuitem(sp_menu, _('Add new family'),
                         handle, self.actions.add_spouse)
            self.add_separator(sp_menu)

            fam_list = person.get_family_handle_list()
            for fam_id in fam_list:
                family = self.dbstate.db.get_family_from_handle(fam_id)
                if family.get_father_handle() == person.get_handle():
                    sp_id = family.get_mother_handle()
                else:
                    sp_id = family.get_father_handle()
                if not sp_id:
                    continue
                spouse = self.dbstate.db.get_person_from_handle(sp_id)
                if not spouse:
                    continue
                self.add_menuitem(sp_menu, displayer.display(spouse),
                                  self.graph_widget.move_to_person,
                                  sp_id, True)

            # go over siblings and build their menu
            item, sib_menu = self.add_submenu(label=_("Siblings"))

            pfam_list = person.get_parent_family_handle_list()
            siblings = []
            step_siblings = []
            for f_h in pfam_list:
                fam = self.dbstate.db.get_family_from_handle(f_h)
                sib_list = fam.get_child_ref_list()
                for sib_ref in sib_list:
                    sib_id = sib_ref.ref
                    if sib_id == person.get_handle():
                        continue
                    siblings.append(sib_id)
                # collect a list of per-step-family step-siblings
                for parent_h in [fam.get_father_handle(),
                                 fam.get_mother_handle()]:
                    if not parent_h:
                        continue
                    parent = self.dbstate.db.get_person_from_handle(
                        parent_h)
                    other_families = [
                        self.dbstate.db.get_family_from_handle(fam_id)
                        for fam_id in parent.get_family_handle_list()
                        if fam_id not in pfam_list]
                    for step_fam in other_families:
                        fam_stepsiblings = [
                            sib_ref.ref for sib_ref in
                            step_fam.get_child_ref_list()
                            if not sib_ref.ref == person.get_handle()]
                        if fam_stepsiblings:
                            step_siblings.append(fam_stepsiblings)

            # add siblings sub-menu with a bar between each siblings group
            if siblings or step_siblings:
                sibs = [siblings] + step_siblings
                for sib_group in sibs:
                    for sib_id in sib_group:
                        sib = self.dbstate.db.get_person_from_handle(
                            sib_id)
                        if not sib:
                            continue
                        if find_children(self.dbstate.db, sib):
                            label = Gtk.Label(
                                label='<b><i>%s</i></b>'
                                % escape(displayer.display(sib)))
                        else:
                            label = Gtk.Label(
                                label=escape(displayer.display(sib)))
                        sib_item = Gtk.MenuItem()
                        label.set_use_markup(True)
                        label.show()
                        label.set_alignment(0, 0)
                        sib_item.add(label)
                        sib_item.connect("activate",
                                         self.graph_widget.move_to_person,
                                         sib_id, True)
                        sib_item.show()
                        sib_menu.append(sib_item)
                    if sibs.index(sib_group) < len(sibs) - 1:
                        self.add_separator(sib_menu)
            else:
                item.set_sensitive(0)

            self.add_children_submenu(person=person)

            # Go over parents and build their menu
            item, par_menu = self.add_submenu(label=_("Parents"))
            no_parents = True
            par_list = find_parents(self.dbstate.db, person)
            for par_id in par_list:
                if not par_id:
                    continue
                par = self.dbstate.db.get_person_from_handle(par_id)
                if not par:
                    continue

                if no_parents:
                    no_parents = False

                if find_parents(self.dbstate.db, par):
                    label = Gtk.Label(label='<b><i>%s</i></b>'
                                      % escape(displayer.display(par)))
                else:
                    label = Gtk.Label(label=escape(displayer.display(par)))

                par_item = Gtk.MenuItem()
                label.set_use_markup(True)
                label.show()
                label.set_halign(Gtk.Align.START)
                par_item.add(label)
                par_item.connect("activate", self.graph_widget.move_to_person,
                                 par_id, True)
                par_item.show()
                par_menu.append(par_item)

            if no_parents:
                # add button to add parents
                add_menuitem(par_menu, _('Add parents'), handle,
                             self.actions.add_parents_to_person)

            # go over related persons and build their menu
            item, per_menu = self.add_submenu(label=_("Related"))

            no_related = True
            for p_id in find_witnessed_people(self.dbstate.db, person):
                per = self.dbstate.db.get_person_from_handle(p_id)
                if not per:
                    continue

                if no_related:
                    no_related = False

                self.add_menuitem(per_menu, displayer.display(per),
                                  self.graph_widget.move_to_person,
                                  p_id, True)
            if no_related:
                item.set_sensitive(0)

            self.add_separator()

            add_menuitem(self, _('Set as home person'),
                         handle, self.actions.set_home_person)

            add_menuitem(self, _('Show path to home person'),
                         handle, self.actions.path_to_home_person)

            # check if we have person in bookmarks
            marks = self.graph_widget.view.bookmarks.get_bookmarks().bookmarks
            if handle in marks:
                add_menuitem(self, _('Remove from bookmarks'), handle,
                             self.actions.remove_from_bookmarks)
            else:
                add_menuitem(self, _('Add to bookmarks'), [handle, person],
                             self.actions.add_to_bookmarks)

            # QuickReports and WebConnect section
            self.add_separator()
            q_exists = self.add_quickreport_submenu(CATEGORY_QR_PERSON, handle)
            w_exists = self.add_web_connect_submenu(handle)

            if q_exists or w_exists:
                self.add_separator()
            self.append_help_menu_entry()

    def add_quickreport_submenu(self, category, handle):
        """
        Adds Quick Reports menu.
        """
        def make_quick_report_callback(pdata, category, dbstate, uistate,
                                       handle, track=[]):
            return lambda x: run_report(dbstate, uistate, category, handle,
                                        pdata, track=track)

        # select the reports to show
        showlst = []
        pmgr = GuiPluginManager.get_instance()
        for pdata in pmgr.get_reg_quick_reports():
            if pdata.supported and pdata.category == category:
                showlst.append(pdata)

        showlst.sort(key=lambda x: x.name)
        if showlst:
            menu_item, quick_menu = self.add_submenu(_("Quick View"))
            for pdata in showlst:
                callback = make_quick_report_callback(
                    pdata, category, self.view.dbstate, self.view.uistate,
                    handle)
                self.add_menuitem(quick_menu, pdata.name, callback)
            return True
        return False

    def add_web_connect_submenu(self, handle):
        """
        Adds Web Connect menu if some installed.
        """
        def flatten(L):
            """
            Flattens a possibly nested list. Removes None results, too.
            """
            retval = []
            if isinstance(L, (list, tuple)):
                for item in L:
                    fitem = flatten(item)
                    if fitem is not None:
                        retval.extend(fitem)
            elif L is not None:
                retval.append(L)
            return retval

        # select the web connects to show
        pmgr = GuiPluginManager.get_instance()
        plugins = pmgr.process_plugin_data('WebConnect')

        nav_group = self.view.navigation_type()

        try:
            connections = [plug(nav_group) if isinstance(plug, abc.Callable) else
                           plug for plug in plugins]
        except BaseException:
            import traceback
            traceback.print_exc()
            connections = []

        connections = flatten(connections)
        connections.sort(key=lambda plug: plug.name)
        if connections:
            menu_item, web_menu = self.add_submenu(_("Web Connection"))

            for connect in connections:
                callback = connect(self.view.dbstate, self.view.uistate,
                                   nav_group, handle)
                self.add_menuitem(web_menu, connect.name, callback)
            return True
        return False

    def family_menu(self, handle):
        """
        Popup menu for family node.
        """
        family = self.dbstate.db.get_family_from_handle(handle)
        if family:
            add_menuitem(self, _('Edit'),
                         handle, self.actions.edit_family)

            add_menuitem(self, _('Delete'),
                         family, self.actions.remove_family)

            self.add_separator()

            # build events submenu
            if len(family.get_event_ref_list()) != 0:
                iteme, evt_menu = self.add_submenu(label=_("Events"))
            else:
                iteme = self.add_menuitem(self, _("No Events for this family"), self.menu_no_action)

            nbe = 0
            for event_ref in family.get_event_ref_list():
                if not event_ref:
                    continue
                nbe += 1
                event = self.dbstate.db.get_event_from_handle(event_ref.ref)
                role = _(event_ref.get_role().xml_str())
                etype = _(event.get_type().xml_str())

                # text = displayer.display(person)
                if event_ref.get_role() != EventRoleType.FAMILY:
                    etype += " (" + role + ") "
                self.add_menuitem(evt_menu, etype,
                                  self.actions.edit_family_event,
                                  family.get_gramps_id(), event, event_ref)

            # build tag submenu
            _item, tag_menu = self.add_submenu(label=_("Tags"))

            add_menuitem(tag_menu, _('Select tags for family'),
                         [handle, 'family'], self.actions.edit_tag_list)

            add_menuitem(tag_menu, _('Organize Tags...'),
                         [handle, 'family'], self.actions.organize_tags)

            self.add_tags_to_menu(family, 'family', tag_menu)

            # build spouses menu
            _item, sp_menu = self.add_submenu(label=_("Spouses"))

            f_handle = family.get_father_handle()
            m_handle = family.get_mother_handle()
            if f_handle:
                spouse = self.dbstate.db.get_person_from_handle(f_handle)
                self.add_menuitem(sp_menu, displayer.display(spouse),
                                  self.graph_widget.move_to_person,
                                  f_handle, True)
            else:
                add_menuitem(sp_menu, _('Add father'), [family, 'father'],
                             self.actions.add_spouse_to_family)

            if m_handle:
                spouse = self.dbstate.db.get_person_from_handle(m_handle)
                self.add_menuitem(sp_menu, displayer.display(spouse),
                                  self.graph_widget.move_to_person,
                                  m_handle, True)
            else:
                add_menuitem(sp_menu, _('Add mother'), [family, 'mother'],
                             self.actions.add_spouse_to_family)

            self.add_children_submenu(family=family)

            # QuickReports section
            self.add_separator()
            q_exists = self.add_quickreport_submenu(CATEGORY_QR_FAMILY, handle)

            if q_exists:
                self.add_separator()
            self.append_help_menu_entry()

    def add_children_submenu(self, person=None, family=None):
        """
        Go over children and build their menu.
        """
        item, child_menu = self.add_submenu(_("Children"))

        no_child = True

        childlist = []
        if family:
            for child_ref in family.get_child_ref_list():
                childlist.append(child_ref.ref)
            # allow to add a child to this family
            add_menuitem(child_menu, _('Add child to family'),
                         family.get_handle(), self.actions.add_child_to_family)
            self.add_separator(child_menu)
            no_child = False
        elif person:
            childlist = find_children(self.dbstate.db, person)

        for child_handle in childlist:
            child = self.dbstate.db.get_person_from_handle(child_handle)
            if not child:
                continue

            if no_child:
                no_child = False

            if find_children(self.dbstate.db, child):
                label = Gtk.Label(label='<b><i>%s</i></b>'
                                  % escape(displayer.display(child)))
            else:
                label = Gtk.Label(label=escape(displayer.display(child)))

            child_item = Gtk.MenuItem()
            label.set_use_markup(True)
            label.show()
            label.set_halign(Gtk.Align.START)
            child_item.add(label)
            child_item.connect("activate", self.graph_widget.move_to_person,
                               child_handle, True)
            child_item.show()
            child_menu.append(child_item)

        if no_child:
            item.set_sensitive(0)

    def add_menuitem(self, menu, label, func, *args):
        """
        Adds menu item.
        """
        item = Gtk.MenuItem(label=label)
        item.connect("activate", func, *args)

        item.show()
        menu.append(item)
        return item

    def add_submenu(self, label):
        """
        Adds submenu.
        """
        item = Gtk.MenuItem(label=label)
        item.set_submenu(Gtk.Menu())
        item.show()
        self.append(item)
        submenu = item.get_submenu()
        submenu.set_reserve_toggle_size(False)
        return item, submenu

    def menu_no_action(self, *args):
        """
        Do nothing
        """
        return True

    def add_separator(self, menu=None):
        """
        Adds separator to menu.
        """
        if menu is None:
            menu = self
        menu_item = Gtk.SeparatorMenuItem()
        menu_item.show()
        menu.append(menu_item)

    def append_help_menu_entry(self):
        """
        Adds help (about) menu entry.
        """
        item = Gtk.MenuItem(label=_("About Graph View"))
        item.connect("activate", self.actions.on_help_clicked)
        item.show()
        self.append(item)


class Actions(Callback):
    """
    Define actions.
    """

    __signals__ = {
        'focus-person-changed' : (str, ),
        'active-changed' : (str, ),
        'rebuild-graph' :  None,
        'path-to-home-person' : (str, bool),
        }

    def __init__(self, dbstate, uistate, bookmarks):
        """
        bookmarks - person bookmarks from GraphView(NavigationView).
        """
        Callback.__init__(self)
        self.dbstate = dbstate
        self.uistate = uistate

        self.bookmarks = bookmarks

    def on_help_clicked(self, widget):
        """
        Display the relevant portion of Gramps manual.
        """
        display_url(WIKI_PAGE)

    def add_spouse(self, obj):
        """
        Add spouse to person (create new family to person).
        See: gramps/plugins/view/relview.py (add_spouse)
        """
        handle = obj.get_data()
        family = Family()
        person = self.dbstate.db.get_person_from_handle(handle)

        if not person:
            return

        if person.gender == Person.MALE:
            family.set_father_handle(person.handle)
        else:
            family.set_mother_handle(person.handle)

        try:
            EditFamily(self.dbstate, self.uistate, [], family)
        except WindowActiveError:
            pass
        # set edited person to scroll on it after rebuilding graph
        self.emit('focus-person-changed', (handle, ))

    def add_spouse_to_family(self, obj):
        """
        Adds spouse to existing family.
        See: editfamily.py
        """
        family, kind = obj.get_data()

        try:
            dialog = EditFamily(self.dbstate, self.uistate, [], family)
            if kind == 'mother':
                dialog.add_mother_clicked(None)
            if kind == 'father':
                dialog.add_father_clicked(None)
        except WindowActiveError:
            pass

    def edit_person(self, obj, person_handle=None):
        """
        Start a person editor for the selected person.
        """
        if not (obj or person_handle):
            return False

        if person_handle:
            handle = person_handle
        else:
            handle = obj.get_data()

        person = self.dbstate.db.get_person_from_handle(handle)
        try:
            EditPerson(self.dbstate, self.uistate, [], person)
        except WindowActiveError:
            pass
        # set edited person to scroll on it after rebuilding graph
        self.emit('focus-person-changed', (handle, ))

    def set_home_person(self, obj):
        """
        Set the home person for database and make it active.
        """
        handle = obj.get_data()
        person = self.dbstate.db.get_person_from_handle(handle)
        if person:
            self.dbstate.db.set_default_person_handle(handle)
            self.emit('active-changed', (handle, ))

    def path_to_home_person(self, obj):
        """
        Draw the relationship between the active and home people
        """
        handle = obj.get_data()
        self.emit('path-to-home-person', (handle, True))

    def edit_family(self, obj, family_handle=None):
        """
        Start a family editor for the selected family.
        """
        if not (obj or family_handle):
            return False

        if family_handle:
            handle = family_handle
        else:
            handle = obj.get_data()

        family = self.dbstate.db.get_family_from_handle(handle)
        try:
            EditFamily(self.dbstate, self.uistate, [], family)
        except WindowActiveError:
            pass

        # set edited family person to scroll on it after rebuilding graph
        f_handle = family.get_father_handle()
        if f_handle:
            self.emit('focus-person-changed', (f_handle, ))
        else:
            m_handle = family.get_mother_handle()
            if m_handle:
                self.emit('focus-person-changed', (m_handle, ))

    def edit_family_event(self, obj, family_id, event, evt_ref):
        """
        Edit the events for this family
        """
        try:
            EditEventRef(self.dbstate, self.uistate, [], event, evt_ref, self.obj_added)
        except WindowActiveError:
            pass

    def edit_person_event(self, obj, person_id, event, evt_ref):
        """
        Edit the events for this person
        """
        try:
            EditEventRef(self.dbstate, self.uistate, [], event, evt_ref, self.obj_added)
        except WindowActiveError:
            pass

    def obj_added(self, reference, primary):
        reference.ref = primary.handle

    def copy_person_to_clipboard(self, obj):
        """
        Renders the person data into some lines of text
        and puts that into the clipboard.
        """
        person_handle = obj.get_data()
        person = self.dbstate.db.get_person_from_handle(person_handle)
        if person:
            _cb = Gtk.Clipboard.get_for_display(Gdk.Display.get_default(),
                                                Gdk.SELECTION_CLIPBOARD)
            format_helper = FormattingHelper(self.dbstate)
            _cb.set_text(format_helper.format_person(person, 11), -1)
            return True
        return False

    def edit_tag_list(self, obj):
        """
        Edit tag list for person or family.
        """
        handle, otype = obj.get_data()
        if otype == 'person':
            target = self.dbstate.db.get_person_from_handle(handle)
            self.emit('focus-person-changed', (handle, ))
        elif otype == 'family':
            target = self.dbstate.db.get_family_from_handle(handle)
            f_handle = target.get_father_handle()
            if f_handle:
                self.emit('focus-person-changed', (f_handle, ))
            else:
                m_handle = target.get_mother_handle()
                if m_handle:
                    self.emit('focus-person-changed', (m_handle, ))
        else:
            return False

        if target:
            tag_list = []
            for tag_handle in target.get_tag_list():
                tag = self.dbstate.db.get_tag_from_handle(tag_handle)
                if tag:
                    tag_list.append((tag_handle, tag.get_name()))

            all_tags = []
            for tag_handle in self.dbstate.db.get_tag_handles(
                    sort_handles=True):
                tag = self.dbstate.db.get_tag_from_handle(tag_handle)
                all_tags.append((tag.get_handle(), tag.get_name()))

            try:
                editor = EditTagList(tag_list, all_tags, self.uistate, [])
                if editor.return_list is not None:
                    tag_list = editor.return_list
                    # Save tags to target object.
                    # Make the dialog modal so that the user can't start
                    # another database transaction while the one setting
                    # tags is still running.
                    pmon = progressdlg.ProgressMonitor(
                        progressdlg.GtkProgressDialog,
                        ("", self.uistate.window, Gtk.DialogFlags.MODAL),
                        popup_time=2)
                    status = progressdlg.LongOpStatus(msg=_("Adding Tags"),
                                                      total_steps=1,
                                                      interval=1 // 20)
                    pmon.add_op(status)
                    target.set_tag_list([item[0] for item in tag_list])
                    if otype == 'person':
                        msg = _('Adding Tags to person (%s)') % handle
                        with DbTxn(msg, self.dbstate.db) as trans:
                            self.dbstate.db.commit_person(target, trans)
                            status.heartbeat()
                    else:
                        msg = _('Adding Tags to family (%s)') % handle
                        with DbTxn(msg, self.dbstate.db) as trans:
                            self.dbstate.db.commit_family(target, trans)
                            status.heartbeat()
                    status.end()
            except WindowActiveError:
                pass

    def organize_tags(self, obj):
        """
        Display the Organize Tags dialog.
        see: .gramps.gui.view.tags
        """
        handle, otype = obj.get_data()
        if otype == 'person':
            target = self.dbstate.db.get_person_from_handle(handle)
            self.emit('focus-person-changed', (handle, ))
        elif otype == 'family':
            target = self.dbstate.db.get_family_from_handle(handle)
            f_handle = target.get_father_handle()
            if f_handle:
                self.emit('focus-person-changed', (f_handle, ))
            else:
                m_handle = target.get_mother_handle()
                if m_handle:
                    self.emit('focus-person-changed', (m_handle, ))

        OrganizeTagsDialog(self.dbstate.db, self.uistate, [])
        self.emit('rebuild-graph')

    def add_tag_to_object(self, obj, data):
        handle, otype, tag_hdle = data
        if otype == 'person':
            target = self.dbstate.db.get_person_from_handle(handle)
            old_tags = target.get_tag_list()
            if tag_hdle in old_tags:
                old_tags.remove(tag_hdle)
            else:
                old_tags.append(tag_hdle)
            target.set_tag_list(old_tags)
            self.emit('focus-person-changed', (handle, ))
            msg = _('Adding Tags to person (%s)') % handle
            with DbTxn(msg, self.dbstate.db) as trans:
                self.dbstate.db.commit_person(target, trans)
        if otype == 'family':
            target = self.dbstate.db.get_family_from_handle(handle)
            old_tags = target.get_tag_list()
            if tag_hdle in old_tags:
                old_tags.remove(tag_hdle)
            else:
                old_tags.append(tag_hdle)
            target.set_tag_list(old_tags)
            msg = _('Adding Tags to family (%s)') % handle
            with DbTxn(msg, self.dbstate.db) as trans:
                self.dbstate.db.commit_family(target, trans)
            self.emit('rebuild-graph')

    def add_parents_to_person(self, obj):
        """
        Open dialog to add parents to person.
        """
        person_handle = obj.get_data()

        family = Family()
        childref = ChildRef()
        childref.set_reference_handle(person_handle)
        family.add_child_ref(childref)
        try:
            EditFamily(self.dbstate, self.uistate, [], family)
        except WindowActiveError:
            return
        # set edited person to scroll on it after rebuilding graph
        self.emit('focus-person-changed', (person_handle, ))

    def add_child_to_family(self, obj):
        """
        Open person editor to create and add child to family.
        """
        family_handle = obj.get_data()
        callback = lambda x: self.__callback_add_child(x, family_handle)
        person = Person()
        name = Name()
        # the editor requires a surname
        name.add_surname(Surname())
        name.set_primary_surname(0)
        family = self.dbstate.db.get_family_from_handle(family_handle)
        # try to get father
        father_handle = family.get_father_handle()
        if father_handle:
            father = self.dbstate.db.get_person_from_handle(father_handle)
            if father:
                preset_name(father, name)

        person.set_primary_name(name)
        try:
            EditPerson(self.dbstate, self.uistate, [], person,
                       callback=callback)
        except WindowActiveError:
            pass

    def __callback_add_child(self, person, family_handle):
        """
        Write data to db.
        Callback from self.add_child_to_family().
        """
        ref = ChildRef()
        ref.ref = person.get_handle()
        family = self.dbstate.db.get_family_from_handle(family_handle)
        family.add_child_ref(ref)

        with DbTxn(_("Add Child to Family"), self.dbstate.db) as trans:
            # add parentref to child
            person.add_parent_family_handle(family_handle)
            # default relationship is used
            self.dbstate.db.commit_person(person, trans)
            # add child to family
            self.dbstate.db.commit_family(family, trans)

    def remove_person(self, obj):
        """
        Remove a person from the database.
        see: libpersonview.py
        """
        person = obj.get_data()

        msg1 = _('Delete %s?') % displayer.display(person)
        msg2 = (_('Deleting the person [%s] will remove it '
                  'from the database.') % person.gramps_id)
        dialog = QuestionDialog2(msg1, msg2,
                                 _("Yes"), _("No"),
                                 self.uistate.window)
        if dialog.run():
            # set the busy cursor, so the user knows that we are working
            self.uistate.set_busy_cursor(True)

            # create the transaction
            with DbTxn('', self.dbstate.db) as trans:
                # create description to save
                description = (_("Delete Person (%s)")
                               % displayer.display(person))

                # delete the person from the database
                # Above will emit person-delete signal
                self.dbstate.db.delete_person_from_database(person, trans)
                trans.set_description(description)

            self.uistate.set_busy_cursor(False)

    def remove_family(self, obj):
        """
        Remove a family from the database.
        see: familyview.py
        """
        family = obj.get_data()

        msg1 = _('Delete family [%s]?') % family.gramps_id
        msg2 = _('Deleting the family will remove it from the database.')
        dialog = QuestionDialog2(msg1, msg2,
                                 _("Yes"), _("No"),
                                 self.uistate.window)
        if dialog.run():
            # set the busy cursor, so the user knows that we are working
            self.uistate.set_busy_cursor(True)

            # create the transaction
            with DbTxn('', self.dbstate.db) as trans:
                # create description to save
                description = _("Delete Family [%s]") % family.gramps_id

                # delete the family from the database
                self.dbstate.db.remove_family_relationships(family.handle,
                                                            trans)
                trans.set_description(description)

            self.uistate.set_busy_cursor(False)

    def add_to_bookmarks(self, obj):
        """
        Adds bookmark for person.
        See: navigationview.py and bookmarks.py
        """
        handle, person = obj.get_data()

        self.bookmarks.add(handle)
        name = displayer.display(person)
        self.uistate.push_message(self.dbstate,
                                  _("%s has been bookmarked") % name)

    def remove_from_bookmarks(self, obj):
        """
        Remove person from the list of bookmarked people.
        See: bookmarks.py
        """
        handle = obj.get_data()
        self.bookmarks.remove_handles([handle])
