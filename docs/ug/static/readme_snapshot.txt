How to get Screen and/or Window Snapshots for Documentation
-----------------------------------------------------------

The SPARK 2014 UG includes a number of screenshots of GPS,
particularly in the tutorial.rst

Here are a few notes on how the screenshots are
best obtained.

1) The shots for release 1 were done on Linux,
running the KDE environment and Window Manager,
using GIMP.

2) Open GIMP, and select File/Create/Screenshot...

3) A small dialog appears.  Select "Take screenshot of a single window"
and DESELCT "Include window decoration" - this makes the shots look
more platform-neutral for all our Windows users.

3) Set "Delay" to something like 5 seconds - enough time to
manipulate GPS into the state you want when the shot is done.

4) Arrange GPS to look _just_ how you want it in the screen shot.
  Which tabs do you want open?
  Which tab in the bottom pane (Messages, Location, or ?)
  Do you need paths and/or error messages highlighted?

  The screenshots in the UG are 1178 pixels wide. This seems
  to give a reasonable balance of size and quality when
  typeset in PDF and HTML.

5) Click "Snap" in the GIMP Screenshot Window

6) Select the GPS Window and make any other
adjustments that you need (like picking a menu item)

7) After the delay, the screenshot will appear in GIMP.

8) Adjust the image as needed (see below).

9) Select "File/Export..."
    Export it as a PNG file with appropriate name.

10) Exit GIMP. There's no need to save the file in GIMP
    own format - just the exported PNG is good enough.

Common Problems
---------------

a) You only get a snapshot of a menu, not the whole window.

   Answer: Click the menu to open it, point the mouse at the
   menu bar, but use the arrow keys to select the menu item
   that you want to highlight.

b) The image still has Window decorations.

   Answer: Use "Tools/Selection Tools/Rectable Select..."
           Select the top window border (it appears to be about
           the top-most 22 pixels in KDE on my machine).
           Select "Select/Invert"
           Select "Image/Crop to Selection"



- Rod Chapman, 28th Feb 2014
