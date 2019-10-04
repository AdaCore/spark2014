.. _manual_proof:

Manual Proof
============

The manual proof is composed of two sides:
- Python plugin for GNAT Studio
- ``Gnat_server`` executable built on Why3

The role of the plugin is to display elements of the interface and allow
interaction with the user. The role of ``gnat_server`` is to safely interact
with the session (like ``Why3``). They communicate using JSON
request/notifications.

.. warning:: The communication between the plugin and the ``itp_server`` *has*
             to be asynchronous. There is no way to know which prover will
             finish its job first so there is no way to know what/when the
             server will notify. Conversely, there is no way to know when the
             user will click on which task.

.. _Python plugin to GNAT Studio:

Python plugin to GNAT Studio
----------------------------

.. warning:: Python plugin is recent work and it is still very hackish.

The GNAT Studio plugin (??? TODO find a way to make a link to this) can be found in the
GNAT Studio repository at ``share/plugins/spark2014/itp_lib.py``.

.. warning:: You should know how to use the ``Python`` console from GNAT Studio. This
             is *****very***** useful. In GNAT Studio, go to
             ``View -> Python Console``, it will start an interactive console
             where you can test all GNAT Studio primitives described in
             http://docs.adacore.com/live/wave/gps/html/gps_ug/GPS.html

.. warning:: Documentation on primitives is found both in:
             http://docs.adacore.com/live/wave/gps/html/gps_ug/GPS.html
             and
             http://docs.adacore.com/gtkada-docs/gtkada_rm/gtkada_rm/


The plugin is called from the ``spark2014.py`` plugin located in
``share/plugins/spark2014.py`` in GNAT Studio repository. It can be used because it was
added as a function ``on_prove_itp`` in the .xml menus launched with SPARK
located in ``share/plugins/spark2014/gnatprove_menus.xml`` and
``share/plugins/spark2014/gnatprove.xml``.

The code of ``itp_lib.py`` is organized in several classes.
``Tree`` class is used to create the Gtk object that is under the
``Proof Tree``.
Roughly speaking, this Gtk element is composed of a model and a view:

.. code-block:: Python

        # A node is (node_ID, parent_ID, name, node_type, color).
        self.model = Gtk.TreeStore(str, str, str, str, str, Gdk.RGBA)
        # Create the view as a function of the model
        self.view = Gtk.TreeView(self.model)

The view describes how the tree will appear in the interface and model is the
underlying datastructure.

The class ``Tree`` describes how to add/remove elements, update them etc...


The main class of this plugin is ``Tree_with_process``. It can be thought of an
extension of ``Tree``. It allows to launch ``gnat_server`` and communicate with
it, create the new consoles and add a ``Tree`` as a proof tree.
We will describe parts of its start function.
This first part is used to define a tree, its state will be changed by function
``check_notifications``.

.. code-block:: Python

        self.tree = Tree()

The following launches a new process ``gnat_server`` (under command variable)
and it also defines the communication with it. Process will be able to write to
the ``stdin`` of the process with ``self.process.send`` function. It will also
read the ``stdout`` of this function: it will trigger the
``self.check_notifications`` each time it reads ``>>>>`` (that particular
string  should not appear anywhere else).

.. code-block:: Python

        self.process = GS.Process(command,
                                  regexp=">>>>",
                                  on_match=self.check_notifications,
                                  directory=dir_gnat_server)


It also launches a console which waits on input and trigger a request to the
server using ``self.interactive_console_input``

.. code-block:: Python

        self.console = GS.Console(ITP_CONSOLE,
                                  on_input=self.interactive_console_input)

The proof task is defined as a regular file:

.. code-block:: Python

        proof_task_file = GS.File(VC_file, local=True)

Functions are provided to parse the JSON notifications of the server, select
nodes in the tree, starting/killing the manual proof etc...


Gnat_server script
------------------

The :download:`gnat_server.ml <../../why3/src/gnat/gnat_server.ml>` script is a
standalone executable used only for communication with a Python plugin in
GNAT Studio. Its input/output are textual JSON data.

The code is mainly decomposed in three parts which are mainly adaptations for
the :download:`itp_server <../../why3/src/session/itp_server.mli>` interface.

Module ``Gnat_Protocol``
^^^^^^^^^^^^^^^^^^^^^^^^

It implements the module ``Protocol`` (from
:download:`itp_server <../../why3/src/session/itp_server.mli>`)

.. code-block:: Ocaml

    module type Protocol = sig

      val get_requests : unit -> ide_request list
      val notify : notification -> unit

    end

These two functions are used by the ``itp_server`` to communicate with the
outside world.

From this, we implicitly add those two functions to handle communication
between stdin/stdout and the ``gnat_server``:

.. code-block:: Ocaml

    Gnat_Protocol.push_one_request_string  : string -> unit
    Gnat_Protocol.communicate_notification : unit -> unit

Internally in Protocol, these just implement Queue which are those two global
variables:

.. code-block:: Ocaml

  let notification_queue = Queue.create ()
  let requests = ref []

For example, ``notify`` add one element to the queue and
``communicate_notification`` takes all the elements from the queue and send
them to ``stdout``


Module ``Gnat_scheduler``
^^^^^^^^^^^^^^^^^^^^^^^^^

It is the ``scheduler`` given as argument to
:download:`itp_server <../../why3/src/session/itp_server.mli>`.

The scheduling function is ``main_loop``. At each invocation of the infinite
loop, it tries to ``select`` one of ``stdin`` and ``stdout`` (for allowance to
read respectively write):

.. code-block:: Ocaml

     let l1, l2, _ = Unix.select [Unix.stdin] output [] timeout in

If it is allowed to read, it reads the ``ide_requests``:

.. code-block:: Ocaml

       if l1 <> [] then
          let rl = read_lines true in
          List.iter Gnat_Protocol.push_one_request_string rl

If it is allowed to write, it communicates all ``notifications`` from the
server:

.. code-block:: Ocaml

      if l2 <> [] then
          while Gnat_Protocol.has_notification () do
            Gnat_Protocol.communicate_notification ()
          done;

After that, it first tries to execute its ``timeout`` functions (if the timings
are ok) and then its ``idle`` one (if no timing was ok for the timeout). After
this execution, it puts back the function on the stack if necessary.

.. code-block:: Ocaml

      match !timeout_handler with
      | (ms,t,f) :: rem when t <= time ->
          timeout_handler := rem;
          let b = f () in
          let time = Unix.gettimeofday () in
          if b then insert_timeout_handler ms (ms +. time) f


Initialization
^^^^^^^^^^^^^^

The third part of this script is the initialization. First, applying the
functor to both modules defined before:

.. code-block:: Ocaml

      module Server = Itp_server.Make (Gnat_Scheduler) (Gnat_Protocol)


Then parsing the commandline, reading the config etc (these were already
covered in GNATWhy3 section).

After initialization, the scheduler starts its infinite loop:

.. code-block:: Ocaml

      let () =
        Gnat_Scheduler.main_loop ()


Why3 itp_server
^^^^^^^^^^^^^^^

The :download:`itp_server <../../why3/src/session/itp_server.mli>` is a Why3
module made to interact with the IDE. The advantage is that its interface is
the ``Protocol`` module: it already uses communication to launch
functions. And these communications functions are those provided by the
``Protocol``.

In this file, one can find wrapper for all the ``schedule_*`` functions, the
way task are printed in ``send_task``, a way of chosing what to do on requests
with function ``treat_request`` (notifications are done everywhere in the file
depending on what is done by the server).


TODO ??? TO BE COMPLETED ??? take example in treat request and schedule_proof_attempt

Transformations with arguments
------------------------------

??? TODO
