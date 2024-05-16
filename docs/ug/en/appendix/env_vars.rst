Environment Variables Used by GNATprove
=======================================

This section describes the environment variables that affect how |GNATprove| operates.

* ``GPR_TOOL`` - This environment variable is intended to be used in GPR
  project files, to specify project settings that depend on the tool. Leaving
  this variable unset when invoking |GNATProve| sets the value to
  ``gnatprove``. See also :ref:`Having Different Switches for Compilation and Verification`.

* ``TMPDIR`` - This variable should contain a path. It controls the place of
  storage for certain internal artifacts. See also :ref:`|GNATprove| and
  Network File Systems or Shared Folders`.

The following environment variables are for internal use, or use by developers,
and shouldn't be set when |GNATProve| is run:

* ``GNSA_ROOT``, ``GNAT2WHY_RAC_INFO``, ``GNAT2WHY_RAC_TRACE``
