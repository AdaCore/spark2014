--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator (dev)
--  Command line arguments: -l ada
--    --pre-process-xmi
--    --clean finnuc.xmi

pragma Style_Checks ("M999");  --  ignore long lines

package finnuc
with
Abstract_State => State
is

   function R_1 (SetA : Boolean; A: Boolean; B : Boolean) return Boolean is
     (if SetA and not B then A else True);
   --  ((not((SetA) and not (B))) or (A)); --De morgans
   --  The set_a command shall lead to a, if b is not already selected, or as a
   --  formal LTL property p1 : G((set_a and not b) -> a)
   function R_2 (SetA : Boolean; C: Boolean; B : Boolean) return Boolean is
     (if SetA and then not C then not B else True);
   --  (((not (SetA)) or C) or B);
   --  The set_a command shall reset b, if c is not active , or
   --  p2 : G((Set_a and not c) -> b)
   --  (if (SetA and not C) then not B else True)
   function R_3
     (SetA : Boolean; SetB : Boolean; A : Boolean; B : Boolean) return Boolean
   is (if SetB and not SetA then B and not A else True);
   --  ((not((SetB) and not (SetA))) or ((B) and not (A)));
   --  The set_b command shall lead to b and reset a, if set_a is not active, or
   --  p3 :G((set_b and not set_a)-> (b and not a))
   -- (if (SetB and not SetA) then (B and not A) else True)
   function R_4 (OldA : Boolean;   C : Boolean;  B : Boolean) return Boolean is
     (if OldA and C then B);
   --  ((not((OldA) and then (C))) or else (B));
   --  If a has been selected, the signal c shall change the selection to b, or
   --  p4 :G((Ya and c) -> b) --(if (OldA and then C) then B else True)
   function R_5 (A : Boolean; B: Boolean) return Boolean is
     (not A or not B);
   --  "Only one mode (a or b) shall be active at the same time", or
   --  p5: G not(a and b)

   procedure init;

   procedure comp
     (SetA : Boolean;
      SetB : Boolean;
      C : Boolean;
      A : out Boolean;
      B : out Boolean;
      OldA : out Boolean)with
     --  Pre => not(SetA and SetB),
     Post => R_1 (SetA, A, B)  -- @COUNTEREXAMPLE
     --  fails when SetA = true, SetB = true and C = false
     --  and then R_2 (SetA, C, B)
     --  and then R_3 (SetA, SetB, A, B)
     --  and then R_4 (OldA, C, B)
     --  and then R_5 (A, B)
     --  fails when B is true from previous step,
     --  SetA = true, SetB = false and C = true
     ;
end finnuc;
--  @EOF
