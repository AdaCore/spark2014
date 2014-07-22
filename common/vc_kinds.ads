------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

--  Changes in VC_Kind should be reflected in
--    - file gnat_expl.ml in gnatwhy3
--    - GPS plug-in spark2014.py
--    - the appendix of SPARK User's Guide

package VC_Kinds is

   type VC_Kind is
      --  VC_RTE_Kind - run-time checks

     (VC_Division_Check,
      VC_Index_Check,
      VC_Overflow_Check,
      VC_Range_Check,
      VC_Length_Check,
      VC_Discriminant_Check,

      --  VC_Assert_Kind - assertions

      VC_Initial_Condition,
      VC_Precondition,               --  the precondition of a call
      VC_Precondition_Main,          --  the precondition of a main program
      VC_Postcondition,              --  a postcondition
      VC_Refined_Post,               --  a refined_post
      VC_Contract_Case,
      VC_Disjoint_Contract_Cases,
      VC_Complete_Contract_Cases,
      VC_Loop_Invariant,
      VC_Loop_Invariant_Init,
      VC_Loop_Invariant_Preserv,
      VC_Loop_Variant,
      VC_Assert,
      VC_Raise,

      --  VC_LSP_Kind - Liskov Substitution Principle

      VC_Weaker_Pre,                  --  pre weaker than classwide pre
      VC_Trivial_Weaker_Pre,          --  specialization of VC_Weaker_Pre when
                                      --  there is no classwide or inherited
                                      --  precondition
      VC_Stronger_Post,               --  post stronger than classwide post
      VC_Weaker_Classwide_Pre,        --  classwide pre weaker than inherited
      VC_Stronger_Classwide_Post);    --  classwide post stronger t/ inherited

   subtype VC_RTE_Kind is VC_Kind range
     VC_Division_Check .. VC_Discriminant_Check;
   subtype VC_Assert_Kind is  VC_Kind range
     VC_Initial_Condition .. VC_Raise;
   subtype VC_LSP_Kind is  VC_Kind range
     VC_Weaker_Pre .. VC_Stronger_Classwide_Post;

   --  Returns True if this kind of VC should be considered like an assertion
   --  when positioning the message to the left-most subexpression of the
   --  checked expression. For example, this is not true for VC_Precondition,
   --  which should be positioned on the location of the call.
   function Locate_On_First_Token (V : VC_Kind) return Boolean is
     (case V is when VC_RTE_Kind  => False,
                when VC_Assert_Kind => V /= VC_Precondition,
                when VC_LSP_Kind    => True);

   SPARK_Suffix : constant String := "spark";

   Flow_Suffix : constant String := "flow";

   Proof_Suffix : constant String := "proof";

end VC_Kinds;
