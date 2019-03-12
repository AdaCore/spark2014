###############
GPS Integration
###############

GPS is the richest of the two IDE integrations, with some features not
available on the command-line of in GNATbench. It has unique features for
launching a GNATprove analysis and for displaying the results.

The plugin detects automatically if the executable ``gnatprove`` is on the PATH
by calling ``os_utils.locate_exec_on_the_path``, in which case it activates
itself and adds corresponding menus in GPS.

The integration of manual proof in GPS is described in :ref:`Python plugin to
GPS`.

User Profile
============

Depending on a user preference (set through the :menuselection:`Preferences`
panel), the proof pop-up panel displayed for the various :menuselection:`SPARK
--> Prove ...` submenus is more or less complex.

The ``Basic`` user profile leads to a stripped down proof panel, with only the
essential choices. In particular, it allows chosing a value of level.

The ``Advanced`` user profile leads to a more detailed proof panel, with
choices for the lower-level switches which make up a given level.

Analysis of Generics
====================

GNATprove only analyzes instances of generics, either:
 - when analyzing the enclosing package/subprogram containing the generic
   instantiation, or
 - when analyzing the generic itself and passing ``-U`` to the command-line so
   that all instantiations of the target generic are analyzed.

In the second case, the GPS plugin automatically adds ``-U`` to the
command-line when it detects that the action (:menuselection:`SPARK -->
Examine` or :menuselection:`SPARK --> Prove`) is applied to a
subprogram/region/line/check inside a generic, by calling
``inside_generic_unit_context``.

Analysis of Subprograms
=======================

When the user right-clicks in an editor, the SPARK plugin detects if the
current cursor location points inside a subprogram (declaration or body) by
calling ``inside_subp_context``. If so, it activates a contextual submenu for
proving the enclosing subprogram. Selecting that submenu calls GNATprove with
``--limit-subp=<location>`` where ``<location>`` points to the declaration of
the subprogram.

Getting that declaration is done by calling ``GPS.Entity`` so it relies on
cross-reference information in GPS, which may be not perfect when the program
has not been compiled previously as the cross-reference information generated
by GNAT is not available in that case. That should be improved in the future
when cross-reference in GPS is provided by Libadalang-based tools.

The switch ``--limit-subp=<location>`` is similarly generated when proving a
region/line of code, as a way to restrict the work in gnat2why to that
subprogram. But these commands work even in the case where no enclosing
subprogram is found. It could probably be passed also when proving a single
check, but is not currently.

Parsing of Messages
===================

The plugin defines a specific parser ``GNATprove_Parser`` for displaying
messages from GNATprove. It relies on the special trailing [#id] being appended
to messages by ``gnatprove`` when switch ``--ide-progress-bar`` is passed
(which is done automatically in the Build Targets defined in
:file:`gnatprove.xml`). This identifier is used in the :file:`.spark` JSON
files to identify message and associate more information to each message, like
its counterexample.

The specific parser fulfils multiple objectives:
 - it adds actions to messages when needed (for example to associate the action
   to display/hide a counterexample),
 - it provides input to ``GPS.Analysis_Tool`` which collects and organizes
   messages by kind and severity, in order to display the interactive Analysis
   Report,
 - it splits the possibly long command-line messages into a main message and
   secondary messages (for the precise unproved property, the counterexample
   and the explanation, when these are present) displayed on separate lines,
 - it associates a severity to the message, so that it is displayed with an
   appropriate background color (which can be customized in
   :menuselection:`Preferences --> Messages` panel).

Counterexamples
===============

When a counterexample is available for a given check message, a magnify icon is
displayed on the left of the message in the ``Locations`` view and on the left
of the corresponding line in the editor. Clicking on this icon causes GPS to
display the counterexample.

The creation of the toggle action to display/hide the counterexample is done in
``act_on_extra_info`` from the GPS plugin, which reads the counterexamples from
the :file:`.spark` files and registers the actions with the icons.
