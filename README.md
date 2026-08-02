# Gramps Graph View Profiles V1.0

Gramps Graph View Profiles extends the **Graph View** add-on for **Gramps 6.0** with reusable Standard and View profiles, startup control, temporary profile use, and ProfileTag filtering.

A Standard profile stores a reusable Graph View setup for one family tree. Named View profiles can also include the Home person and Active person.

> This is an independent and unofficial extension. It is not affiliated with or endorsed by the Gramps Project or the original Graph View developers.

## Features

- Reusable Standard profiles
- Named View profiles
- Startup selection: no profile, Standard profile, or current View profile
- Temporary profile use with restoration when the family tree is closed
- One-time backup of the original Graph View settings
- ProfileTag filtering from Configure and the right-click menu
- Save, load, overwrite, and delete controls
- Validation of profile files, family-tree information, saved people, and supported settings
- Support for zoom and chart position
- Optional Danish translation

## Requirements

- Gramps 6.0
- Graph View add-on

Tested with Gramps 6.0.8 on Windows 11 and Zorin OS 18.1 Core. macOS has not been tested.

## Installation

1. Close the family tree and exit Gramps.
2. Open:

   ```text
   C:\Users\<your-name>\AppData\Roaming\gramps\gramps60\plugins\GraphView
   ```

3. Rename the existing `graphview.py` to `graphview.py.bak`.
4. Copy the supplied `graphview.py` into the GraphView folder.
5. Start Gramps, open the family tree, and select Graph View.
6. Open **Configure → Profiles** and enable the profile function.

The release ZIP also contains `README.txt`, `LICENSE.txt`, `RELEASE_NOTES.txt`, and the optional Danish translation `addon.mo`.

## Optional Danish translation

Copy `addon.mo` into:

```text
C:\Users\<your-name>\AppData\Roaming\gramps\gramps60\plugins\GraphView\locale\da\LC_MESSAGES
```

Rename any existing `addon.mo` first if it must be retained.

## Profile storage

Standard profiles, startup settings, the original settings backup, and temporary restore files are stored in the shared `GraphView/profiles` folder.

View profiles are stored separately in the base media folder of each family tree. No profile settings are added to `Gramps.ini`.

## ProfileTag

A person tag named `ProfileTag` can limit the graph to tagged people that Graph View can connect within the displayed graph.

ProfileTag filtering can be selected independently of the profile function from the Layout tab or the Graph View right-click menu.

## Downloads and documentation

Installation packages, documentation, and usage notes are also available at [myown-project.dk](https://myown-project.dk/).

## Questions and support

For general questions, installation help, and usage discussions, use GitHub Discussions.

For reproducible bugs and feature requests, use GitHub Issues.

## License

The original Graph View source code is distributed under the GNU General Public License, version 2 or, at your option, any later version. This modified version remains under the same terms. See [LICENSE](LICENSE).

## Disclaimer

This software is provided “as is”, without warranty of any kind. Use it at your own risk. The author is not liable for loss of data or any other damage arising from its use.
