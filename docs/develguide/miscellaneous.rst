#############
Miscellaneous
#############

This part reference documentation for specific part that are not directly
gnatprove but that are useful to developpers.

.. _Integration:

*********************
Integration Testsuite
*********************

This part contains informations on how to setup and use the integration
testsuite. This only introduces the GPS/SPARK interaction in this testsuite not
the rest. The integration testsuite tests the behavior of tools combined with
each others. For example, there are tests checking that GPS works with
SPARK. These tests are written using an X environnment simulator called Xvcd and
the plugin documentation of GPS
(see http://docs.adacore.com/gps-docs/users_guide/_build/html/GPS.html) which
virtually allows you to simulate any behavior of GPS that you would be able to
do in a plugin.
The integration testsuite is located in
``git.adacore.com/integration_testsuite``.


Documentation
=============

Documentation for this testsuite can be found in the repo itself and in the
SPARK wiki which quickly describes how to run test.

Execute test
============

To execute tests using GPS and SPARK, you will need to install Xvcd first. Then
check that SPARK and GPS are indeed installed and do:

``./testsuite --with-tools=spark,gps``

This will launch the complete integration testsuite (majority of which will be
PASSED as you didn't specify other tools such as gnatcov).


Composition of a test
=====================

This testsuite can be understood as the discussion between a driver and a
test: this seems to be necessary as GPS is interactive so orders can always be
given to it (in order to make it sequential, you need this kind of
interaction).
The tests are not check for their output: instead you will add assertions into
your code which the test will check. For example, you can check that you have
at least one message after the execution of something.

The organization of tests is different than it is in the standards testsuite
for SPARK. The test is composed of two files (it can also contain Ada code files).

The ``test.yaml`` file contains the dependencies, description, requiremenets
and targets of your test. It also serves as a ``test.opt`` file:

- ``description:`` quick description of your test
- ``driver:`` the driver that you will use (we will assume we always use gps
  here)
- ``ressources:`` these are the source ada files that you want to use your test
  on. Historically, these files seem to be located under ``shared/`` (you can 
  apparently use files located directly in the test too).
- ``requires`` tools that are required for your test
- ``targets`` target for your test (for embedded). SPARK is not embedded, use
  native.
- ``expect_failure`` use this if you want to XFAIL the test

The ``test.py`` file is the script of your test. It will be launched by a
driver for test and you will be able to stop execution or wait for tasks to
finish using the python command ``yield``.
You can find an example of script test in ``shared/gps_support/spark.py`` file
under this repo.

Writing a test
==============

To write the ``test.py`` file, you can launch any function from the plugin
``spark2014.py`` or from GPS plugin library.
Few things to know:

- First thing you should do is load the project:
  ``yield load_project_file(project_file)``
- Use ``yield wait_tasks()`` to let GPS finish process your command before
  continuing
- Put assertions  in your code to do the testing
- To test your tests you can run ``testsuite`` and then go to
  ``out/new/*.yaml``. This is a file containing the log and debug information
  of your test.
