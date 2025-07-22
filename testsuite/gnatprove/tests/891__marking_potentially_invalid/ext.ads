pragma Partition_Elaboration_Policy (Sequential);
pragma Profile (Jorvik);

package Ext with Spark_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type R is record
      I : aliased Positive;
   end record;

   --  VIOLATIONS

   --  No scalar result unless the function is imported

   function F_Scalar_Imported return Positive with
     Potentially_Invalid => F_Scalar_Imported'Result, Import;

   function F_Scalar_Body return Positive with
     Potentially_Invalid => F_Scalar_Body'Result;

   --  No concurrent type

   protected type Prot_Typ is
      function Get return Integer;
   private
      X : Integer := 0;
   end Prot_Typ;

   P : Prot_Typ with Potentially_Invalid;

   task type Task_Typ;

   Tk : Task_Typ with Potentially_Invalid;

   --  No Part_Of

   protected Single_Prot is
      function Get return Integer;
   private
      X : Integer := 0;
   end Single_Prot;

   X : R := (I => 1) with Part_Of => Single_Prot, Potentially_Invalid;

   --  No access types

   type R_Acc is access R;

   Acc : R_Acc with Potentially_Invalid;

   type R_Acc_Array is array (1 .. 10) of R_Acc;

   Acc_A : R_Acc_Array with Potentially_Invalid;

   type R_Acc_Rec is record
      F : R_Acc;
   end record;

   Acc_R : R_Acc_Rec with Potentially_Invalid;

   --  No ownership types

   package Nested_Own is
      type T_Own is private with
        Annotate => (GNATprove, Ownership);
   private
      pragma SPARK_Mode (Off);
      type T_Own is new Integer;
   end Nested_Own;
   use Nested_Own;

   Ow : T_Own with Potentially_Invalid;

   type Own_Array is array (1 .. 10) of T_Own;

   Own_A : Own_Array with Potentially_Invalid;

   type Own_Rec is record
      F : T_Own;
   end record;

   Own_R : Own_Rec with Potentially_Invalid;

   --  No tagged types

   type Tag is tagged null record;

   Tg : Tag with Potentially_Invalid;

   type Tag_Array is array (1 .. 10) of Tag;

   Tag_A : Tag_Array with Potentially_Invalid;

   type Tag_Rec is record
      F : Tag;
   end record;

   Tag_R : Tag_Rec with Potentially_Invalid;

   --  No unchecked union

   type UU (P : Boolean := True) is record
      case P is
      when True =>
         F : Integer;
      when others =>
         null;
      end case;
   end record with Unchecked_Union;

   U : UU with Potentially_Invalid;

   type UU_Array is array (1 .. 10) of UU;

   UU_A : UU_Array with Potentially_Invalid;

   type UU_Rec is record
      F : UU;
   end record;

   UU_R : UU_Rec with Potentially_Invalid;

   --  No invariant

   package Nested_Inv is
      type T_Inv is private;
   private
      type T_Inv is new Integer with Type_Invariant => T_Inv > 0;
   end Nested_Inv;

   X_Inv : Nested_Inv.T_Inv with Potentially_Invalid;

   type T_Inv is new Nested_Inv.T_Inv;

   Y_Inv : T_Inv with Potentially_Invalid;

   --  Potentially_Invalid is not allowed on dispatching operations

   package Nested_Disp is
      type Root is tagged null record;

      procedure P (X : Root; Y : R) with
        Import,
        Potentially_Invalid => Y;

      function F (X : Root) return R with
        Import,
        Potentially_Invalid => F'Result;
   end Nested_Disp;

   --  Potentially_Invalid on the primitive equality of a record type

   type R_Eq is new R;

   function "=" (X, Y : R_Eq) return Boolean with
     Import,
     Potentially_Invalid => (X, Y);

   --  Overlays

   X_Overlay_1 : R := (I => 13) with Potentially_Invalid;
   Y_Overlay_1 : Integer with Import, Address => X_Overlay_1'Address;

   X_Overlay_2 : Integer := 13;
   Y_Overlay_2 : R with Potentially_Invalid, Import, Address => X_Overlay_2'Address;

   --  TOOL RESTRICTIONS

   --  Predicates

   type T_Pred is new Integer with Predicate => T_Pred > 0;

   X_Pred : T_Pred with Potentially_Invalid;

   type T_Pred_2 is new T_Pred;

   Y_Pred : T_Pred_2 with Potentially_Invalid;

   --  Mutable discriminants

   type Mut (P : Boolean := True) is record
      case P is
      when True =>
         F : Integer;
      when others =>
         null;
      end case;
   end record;

   M : Mut with Potentially_Invalid;

   type Mut_Array is array (1 .. 10) of Mut;

   Mut_A : Mut_Array with Potentially_Invalid;

   type Mut_Rec is record
      F : Mut;
   end record;

   Mut_R : Mut_Rec with Potentially_Invalid;

   --  Relaxed initialization

   type Relaxed is new R with Relaxed_Initialization;

   RR : Relaxed with Potentially_Invalid;

   type Relaxed_Array is array (1 .. 10) of Relaxed;

   Relaxed_A : Relaxed_Array with Potentially_Invalid;

   type Relaxed_Rec is record
      F : Relaxed;
   end record;

   Relaxed_R : Relaxed_Rec with Potentially_Invalid;

   RR_2 : R with Potentially_Invalid, Relaxed_Initialization;

   function F_Relaxed return R with
     Potentially_Invalid => F_Relaxed'Result,
     Relaxed_Initialization => F_Relaxed'Result;

   procedure P_Relaxed (X : R) with
     Potentially_Invalid => X,
     Relaxed_Initialization => X;

   --  Volatile objects

   type R_Vol is new R with Volatile;

   Vol1 : R_Vol with Potentially_Invalid;

   Vol2 : R with Volatile, Potentially_Invalid;

   function F_Vol (X : R_Vol) return Integer with Volatile_Function, Potentially_Invalid => X;

   function F_Vol_2 (X : Integer) return R_Vol with Volatile_Function, Potentially_Invalid => F_Vol_2'Result;

   --  Private types

   package Nested_Priv is
      type T_Priv is private;
   private
      pragma SPARK_Mode (Off);
      type T_Priv is new Integer;
   end Nested_Priv;
   use Nested_Priv;

   Pr : T_Priv with Potentially_Invalid;

   type Priv_Array is array (1 .. 10) of T_Priv;

   Priv_A : Priv_Array with Potentially_Invalid;

   type Priv_Rec is record
      F : T_Priv;
   end record;

   Priv_R : Priv_Rec with Potentially_Invalid;

   --  Access subprogram

   type F_Acc is access function return R;

   function FF return R with Potentially_Invalid => FF'Result;

   F_Acc_Obj : constant F_Acc := FF'Access;

   --  Iterable

   type T_Iter is record
      F : Positive;
      L : Natural;
   end record with
     Iterable => (First => First, Next => Next, Has_Element => Has_Element);

   function First (C : T_Iter) return Positive is (C.F) with
     Potentially_Invalid => C;

   function Next (C : T_Iter; P : Positive) return Positive is (P + 1);

   function Has_Element (C : T_Iter; P : Positive) return Boolean is (P <= C.F);

   --  Borrowed/Observed parameter

   function Observe (X : aliased R) return access constant Positive is
     (X.I'Access) with
     Potentially_Invalid => X;

   function Borrow (X : aliased in out R) return access Positive is
     (X.I'Access) with
     Potentially_Invalid => X;

   --  Logical equality

   function Logic_Eq (X, Y : R) return Boolean with
     Potentially_Invalid => (X, Y),
     Annotate => (GNATprove, Logical_Equal);

   --  Inline for proof, invalid result is not OK if the function has a post

   function F_Inlined_Param (X : R) return R with
     Potentially_Invalid => X,
     Post => F_Inlined_Param'Result = X,
     Annotate => (GNATprove, Inline_For_Proof);

   function F_Inlined_Expr (X : R) return R is
     (X)
   with
     Potentially_Invalid => F_Inlined_Expr'Result,
     Annotate => (GNATprove, Inline_For_Proof);

   function F_Inlined_Res (X : R) return R with
     Potentially_Invalid => F_Inlined_Res'Result,
     Post => F_Inlined_Res'Result = X,
     Annotate => (GNATprove, Inline_For_Proof);

   --  WARNINGS

   --  Types with no invalid values

   type R_Val is record
      I : Integer;
   end record;

   X_Val : R_Val with Potentially_Invalid;

   function F_Val return R_Val with
     Potentially_Invalid => F_Val'Result;

   procedure P_Val (X : R_Val) with
     Potentially_Invalid => X;

   --  Use of potentially invalid objects in postconditions of imported
   --  subprograms. Warnings should only be emitted on occurrence that are not
   --  completely guarded.

   --  Read of function result, we expect a warning

   function Read (X : Integer) return Positive with
     Global => null,
     Import,
     Potentially_Invalid => Read'Result,
     Post => Read'Result = X;

   --  Read of parameter, we expect a warning

   procedure P_Read (X : Integer; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => Res.I = X;

   --  Read of function call, we expect a warning

   procedure P_Call_Func (X : Integer) with
     Import,
     Post => X = Read (X);

   G : R with Potentially_Invalid;

   --  Read of global variable, we expect a warning

   procedure P_Write_G (X : Integer) with
     Import,
     Global => (In_Out => G),
     Post => X = G.I;

   --  On procedures that have a body in SPARK, we do not expect a warning,
   --  unless proof is disabled.

   procedure P_Body_SPARK (X : Integer; Res : out R) with
     Potentially_Invalid => Res,
     Post => Res.I = X;

   --  Guarded reads in conditionals

   procedure P_Read_Then_OK (X : Integer; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (if Res'Valid_Scalars then Res.I = X);

   procedure P_Read_Else_OK (X : Integer; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (if not Res'Valid_Scalars then true else Res.I = X);

   procedure P_Read_Then_KO (X : Integer; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (if not Res'Valid_Scalars then Res.I = X);

   procedure P_Read_Else_KO (X : Integer; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (if Res'Valid_Scalars then true else Res.I = X);

   procedure P_Read_Or_OK (X : Integer; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => not Res'Valid_Scalars or else Res.I = X;

   procedure P_Read_Or_KO (X : Integer; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => Res'Valid_Scalars or else Res.I = X;

   procedure P_Read_And_OK (X : Positive; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => Res'Valid_Scalars and then Res.I = X;

   procedure P_Read_And_KO (X : Positive; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => not Res'Valid_Scalars and then Res.I = X;

   procedure P_Read_And_Nested_Pos_OK (B : out Boolean; X : Positive; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (Res'Valid_Scalars and B) and then Res.I = X;

   procedure P_Read_And_Nested_Neg_OK (B : out Boolean; X : Positive; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (not Res'Valid_Scalars and (B or not Res'Valid_Scalars)) or else Res.I = X;

   procedure P_Read_And_Nested_Neg_KO (B : out Boolean; X : Positive; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (not Res'Valid_Scalars and B) or else Res.I = X;

   procedure P_Read_Or_Nested_Pos_OK (B : out Boolean; X : Positive; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (Res'Valid_Scalars or (B and Res'Valid_Scalars)) and then Res.I = X;

   procedure P_Read_Or_Nested_Pos_KO (B : out Boolean; X : Positive; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (Res'Valid_Scalars or B) and then Res.I = X;

   procedure P_Read_Or_Nested_Neg_OK (B : out Boolean; X : Positive; Res : out R) with
     Import,
     Potentially_Invalid => Res,
     Post => not Res'Valid_Scalars or else Res.I = X;

   --  Guarded reads on inputs

   procedure P_Read_Old_OK_1 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Post => Boolean'(if Res'Valid_Scalars then Res.I = 0)'Old;

   procedure P_Read_Old_OK_2 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (if Res'Valid_Scalars'Old then Res'Old.I = 0);

   procedure P_Read_Old_OK_3 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (if Res'Old'Valid_Scalars then Res'Old.I = 0);

   procedure P_Read_Old_OK_4 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Contract_Cases => (Res'Valid_Scalars => Res'Old.I = 0, others => True);

   procedure P_Read_Old_OK_5 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Contract_Cases => (Res'Valid_Scalars => Boolean'(Res.I = 0)'Old, others => True);

   procedure P_Read_Old_OK_6 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Pre => Res'Valid_Scalars,
     Post => Boolean'(Res.I = 0)'Old;

   procedure P_Read_Old_OK_7 (Res : R) with
     Import,
     Potentially_Invalid => Res,
     Pre => Res'Valid_Scalars,
     Post => Res.I = 0;

   procedure P_Read_Old_OK_8 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Contract_Cases => (not Res'Valid_Scalars => True, others => Boolean'(Res.I = 0)'Old);

   procedure P_Read_Old_OK_9 (Res : in out R; B : Boolean) with
     Import,
     Potentially_Invalid => Res,
     Contract_Cases => (B and Res'Valid_Scalars => Res'Old.I = 0, not Res'Valid_Scalars => True, others => Boolean'(Res.I = 0)'Old);

   procedure P_Read_Old_KO_1 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (if Res'Valid_Scalars then Boolean'(Res'Old.I = 0));

   procedure P_Read_Old_KO_2 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (if Res'Old'Valid_Scalars then Boolean'(Res.I = 0));

   procedure P_Read_Old_KO_3 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Post => (if Res'Old'Valid_Scalars then Boolean'(Res.I = 0)'Old);

   procedure P_Read_Old_KO_4 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Contract_Cases => (Res'Valid_Scalars => Res.I = 0, others => True);

   procedure P_Read_Old_KO_5 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Pre => Res'Valid_Scalars,
     Post => Res.I = 0;

   procedure P_Read_Old_KO_6 (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Contract_Cases =>
       (Res.I = 0 => True,
        others    => Res.I = 0);

   procedure P_Read_Old_KO7 (Res : in out R; B : Boolean) with
     Import,
     Potentially_Invalid => Res,
     Contract_Cases => (not Res'Valid_Scalars and B => True, Res'Valid_Scalars and not B => True, others => Boolean'(Res.I = 0)'Old);

   procedure P_Read_Attr (Res : in out R) with
     Import,
     Potentially_Invalid => Res,
     Post => Res'Valid_Scalars and then Res'Old'Update (I => 12) = Res;

end Ext;
