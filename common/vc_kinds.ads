------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

--  This package defines the different kinds of VCs that we generate in
--  Gnat2why. The run-time checks correspond to Ada RM checks, for which the
--  front-end defines distinct constants in types.ads. Here, we use a new
--  enumeration instead of these constants, because we are only interested in
--  run-time errors that can happen in SPARK code (e.g. it excludes
--  Access_Check), and which GNATprove can detect (it excludes
--  Storage_Check), plus various assertions that we want to distinguish.

--  Changes in VC_Kind should be reflected in gnat_expl.ml in gnatwhy3, the
--  driver for VC generation and proof.

package VC_Kinds is

   type VC_Kind is
      --  Run-time checks

     (VC_Unused,
      VC_Division_Check,
      VC_Index_Check,
      VC_Overflow_Check,
      VC_Range_Check,
      VC_Length_Check,
      VC_Discriminant_Check,

      --  Assertions

      VC_Initial_Condition,
      VC_Precondition,
      VC_Postcondition,
      VC_Contract_Case,
      VC_Disjoint_Contract_Cases,
      VC_Complete_Contract_Cases,
      VC_Loop_Invariant,
      VC_Loop_Invariant_Init,
      VC_Loop_Invariant_Preserv,
      VC_Loop_Variant,
      VC_Assert);

   function Is_Assertion_Kind (V : VC_Kind) return Boolean is
     (V in
        VC_Postcondition |
        VC_Loop_Invariant |
        VC_Assert);

   Proof_Suffix : constant String := ".proof";

end VC_Kinds;
