------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or modify it  --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnatprove is distributed in the hope that it will  be  useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package VC_Kinds is
   --  This package defines the different kinds of VCs that we generate in
   --  Gnat2why.

   type VC_Kind is (
      VC_Unused,
      VC_Overflow_Check,
      VC_Range_Check,
      VC_Array_Bounds_Check,
      VC_Division_By_Zero,
      VC_Precondition,
      VC_Postcondition,
      VC_Loop_Invariant,
      VC_Loop_Invariant_Init,
      VC_Loop_Invariant_Preserv,
      VC_Assert
   );

end VC_Kinds;
