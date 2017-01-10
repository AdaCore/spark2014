package Default_Init with SPARK_Mode is

   type Rec is private with
     Default_Initial_Condition => Rec_Ok (Rec);
   type Arr is private with
     Default_Initial_Condition => Arr_Ok (Arr);
   type Nat is private with
     Default_Initial_Condition => Nat_Ok (Nat);
   type Wrong is private with --@DEFAULT_INITIAL_CONDITION:FAIL
     Default_Initial_Condition => Wrong_Ok (Wrong);
   type Rte is private with
     Default_Initial_Condition => Rte_Ok (Rte); --@PRECONDITION:FAIL
   type Glob1 is private with --@DEFAULT_INITIAL_CONDITION:FAIL
     Default_Initial_Condition => Glob1_Ok (Glob1);
   type Glob2 is private with --  @DEFAULT_INITIAL_CONDITION:FAIL
     Default_Initial_Condition => Glob2_Ok (Glob2);
   type Discr (B : Boolean) is private with
     Default_Initial_Condition => Discr_Ok (Discr);
   type Mut_Discr (B : Boolean := False) is private with --  @DEFAULT_INITIAL_CONDITION:FAIL
     Default_Initial_Condition => Mut_Discr_Ok (Mut_Discr);

   function Rec_Ok (X : Rec) return Boolean;
   function Arr_Ok (X : Arr) return Boolean;
   function Nat_Ok (X : Nat) return Boolean;
   function Wrong_Ok (X : Wrong) return Boolean;
   function Pre_Rte_Ok return Boolean;
   function Rte_Ok (X : Rte) return Boolean with
     Pre => Pre_Rte_Ok;
   function Glob1_Ok (X : Glob1) return Boolean;
   function Glob2_Ok (X : Glob2) return Boolean;
   function Discr_Ok (X : Discr) return Boolean;
   function Mut_Discr_Ok (X : Mut_Discr) return Boolean;

   procedure Def_Priv;

   procedure Def_Simple;

   procedure Def_Wrong;

   procedure Def_Rte;

   procedure Def_Glob1;

   procedure Def_Glob2;

   procedure Def_Discr;

private
   N : Natural;

   function Init (X : Natural) return Natural with
     Pre => True;

   type Rec is record
      F : Natural := 0;
   end record;

   type Arr is array (1 .. 3) of Natural with
     Default_Component_Value => 0;

   type Nat is new Natural with Default_Value => 0;

   type Wrong is new Natural with Default_Value => 0;

   type Rte is array (1 .. 3) of Nat;

   type Glob1 is record
      F : Natural := 0;
   end record;

   type Glob2 is record
      F : Natural := 0;
   end record;

   type Discr (B : Boolean) is record
      case B is
         when False => null;
         when True  => F : Natural := 0;
      end case;
   end record;

   type Mut_Discr (B : Boolean := False) is record
      case B is
         when False => null;
         when True  => F : Natural := Init (0);
      end case;
   end record;

   function Rec_Ok (X : Rec) return Boolean is (X.F = 0);
   function Arr_Ok (X : Arr) return Boolean is (X (1) = 0);
   function Nat_Ok (X : Nat) return Boolean is (X = 0);
   function Wrong_Ok (X : Wrong) return Boolean is (X = Wrong (Init (0)));
   function Pre_Rte_Ok return Boolean is (N in Rte'Range);
   function Rte_Ok (X : Rte) return Boolean is (X (1) = 0);
   function Glob1_Ok (X : Glob1) return Boolean is (X.F = N);
   function Glob2_Ok (X : Glob2) return Boolean is (X.F = N);
   function Discr_Ok (X : Discr) return Boolean is
     (if X.B then X.F = 0);
   function Mut_Discr_Ok (X : Mut_Discr) return Boolean is (not X.B);

end;
