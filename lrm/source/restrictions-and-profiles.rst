Restrictions and Profiles
=========================


By section

.. csv-table::
   :header:  "Section", "Restriction", "Effect"

   "6.1", "No_Default_Subprogram_Parameters", "Prohibits the use of default subprogram parameters, that is, a ``parameter_specification`` cannot have a ``default_expression``."
   "6.2", "Strict_Modes", "``Strict_Modes`` requires: (a) A *formal parameter* (see Ada LRM 6.1) of a subprogram of mode **in** or **in out** must be read directly or indirectly on at least one executable path, or used in the initialization of a declaration, within the subprogram body. (b) A *formal parameter* of a subprogram of mode **out** or **in out** must be updated directly or indirectly on at least executable path, or used in the initialization of a declaration, within the subprogram body."



