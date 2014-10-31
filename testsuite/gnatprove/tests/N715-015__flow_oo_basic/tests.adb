with Foo; use Foo;
with Other;

package body Tests is

   pragma Warnings (Off, "subprogram * has no effect");
   pragma Warnings (Off, "analyzing unreferenced *");

   type Pair is record
      A : Widget_T;
      B : Nice_Widget_T;
   end record;

   function F_Get_Item   (W : Widget_T) return Boolean;
   function F_Get_Item_C (W : Widget_T'Class) return Boolean;
   function F_Get_Item_E (W : Widget_T) return Boolean with Extensions_Visible;

   procedure P_Get_Item   (W : Widget_T;
                           B : out Boolean)
   with Global => null;
   procedure P_Get_Item_C (W : Widget_T'Class;
                           B : out Boolean)
   with Global => null;
   procedure P_Get_Item_E (W : Widget_T;
                           B : out Boolean)
   with Global => null,
        Extensions_Visible;

   procedure P_Mod_Item (W : in out Widget_T;
                         N : Integer)
   with Global => null;
   procedure P_Mod_Item_C (W : in out Widget_T'Class;
                           N : Integer)
   with Global => null;
   procedure P_Mod_Item_E (W : in out Widget_T;
                           N : Integer)
   with Global => null,
        Extensions_Visible;

   function F_Get_Item   (W : Widget_T) return Boolean
   is (W.Hash > 0);

   function F_Get_Item_C (W : Widget_T'Class) return Boolean
   is (W.Hash > 0);

   function F_Get_Item_E (W : Widget_T) return Boolean
   is (F_Get_Item_C (W));

   procedure P_Get_Item   (W : Widget_T;
                           B : out Boolean)
   is
   begin
      B := F_Get_Item (W);
   end P_Get_Item;

   procedure P_Get_Item_C (W : Widget_T'Class;
                           B : out Boolean)
   is
   begin
      B := F_Get_Item_C (W);
   end P_Get_Item_C;

   procedure P_Get_Item_E (W : Widget_T;
                           B : out Boolean)
   is
   begin
      B := F_Get_Item_E (W);
   end P_Get_Item_E;

   procedure P_Mod_Item (W : in out Widget_T;
                         N : Integer)
   is
   begin
      W.X := N;
   end P_Mod_Item;

   procedure P_Mod_Item_C (W : in out Widget_T'Class;
                           N : Integer)
   is
   begin
      W.X := W.Hash;
      W.Y := N;
   end P_Mod_Item_C;

   procedure P_Mod_Item_E (W : in out Widget_T;
                           N : Integer)
   is
   begin
      P_Mod_Item_C (W, N);
      W.X := 0;
      W.Y := 0;
   end P_Mod_Item_E;

   --  All annotations are meant to be `correct', so this test should not
   --  produce any messages.

   --  Root is a null record, so although the result here is odd its right.
   --  Extensions are not visible, so again this is correct.
   procedure Test_01 (Obj : in     Root_T;
                      N   :    out Natural)
   with Global  => null,
        Depends => (N => null)
   is
   begin
      N := Obj.Hash;
   end Test_01;

   --  Ditto here, even though extensions are visible, the hash function
   --  we've called does not make use of any extensions, and we don't
   --  dispatch here.
   procedure Test_01_E (Obj : in     Root_T;
                        N   :    out Natural)
   with Global  => null,
        Depends => (N => null),
        Extensions_Visible
   is
   begin
      N := Obj.Hash;
   end Test_01_E;

   procedure Test_02 (Obj : in     Widget_T;
                      N   :    out Natural)
   with Global  => null,
        Depends => (N => Obj)
   is
   begin
      N := Obj.Hash;
   end Test_02;

   procedure Test_03 (Obj : in     Root_T'Class;
                      N   :    out Natural)
   with Global  => null,
        Depends => (N => Obj)
   is
   begin
      N := Obj.Hash;
   end Test_03;

   procedure Test_04 (Obj : in     Widget_T'Class;
                      N   :    out Natural)
   with Global  => null,
        Depends => (N => Obj)
   is
   begin
      N := Obj.Hash;
   end Test_04;

   --  View conversions.
   procedure Test_05 (A, B : in     Integer;
                      C    : in     Boolean;
                      N    :    out Natural)
   with Global  => null,
        Depends => (N => (A, B),
                    null => C)
   is
      Obj : constant Nice_Widget_T := (X     => A,
                                       Y     => B,
                                       Round => C);
      Tmp : Widget_T := Widget_T (Obj);
   begin
      N := Tmp.Hash;
   end Test_05;

   procedure Test_06 (A, B : in     Integer;
                      C    : in     Boolean;
                      N    :    out Natural)
   with Global  => null,
        Depends => (N => (A, B),
                    null => C)
   is
      Obj : constant Nice_Widget_T := (X     => A,
                                       Y     => B,
                                       Round => C);
   begin
      N := Widget_T (Obj).Hash;
   end Test_06;

   procedure Test_07 (A, B : in     Integer;
                      C    : in     Boolean;
                      N    :    out Natural)
   with Global  => null,
        Depends => (N => C,
                    null => (A, B))
   is
      Obj : Nice_Widget_T := (X     => A,
                              Y     => B,
                              Round => C);
   begin
      --  Clear X and Y
      Zero_Widget (Widget_T (Obj));
      N := Obj.Hash;
   end Test_07;

   procedure Test_08 (A, B : in     Integer;
                      C    : in     Boolean;
                      N    :    out Natural)
   with Global  => null,
        Depends => (N    => null,
                    null => (A, B, C))
   is
      pragma Warnings (Off, "initialization has no effect");
      Obj : Nice_Widget_T := (X     => A,
                              Y     => B,
                              Round => C);
      pragma Warnings (On, "initialization has no effect");
   begin
      --  Clear everything
      Zero_Widget (Obj);
      N := Obj.Hash;
   end Test_08;

   --  Test view conversions of record fields.
   procedure Test_09 (A, B : in     Integer;
                      C    : in     Boolean;
                      N    :    out Natural)
   with Global  => null,
        Depends => (N => (A, B),
                    null => C)
   is
      Obj : constant Nice_Widget_T := (X     => A,
                                       Y     => B,
                                       Round => C);
      Tmp : Pair := (A => Widget_T (Obj),
                     B => Obj);
      Tmp2 : Widget_T := Widget_T (Tmp.B);
   begin
      N := Tmp2.Hash;
   end Test_09;

   --  Testing update attributes
   procedure Test_10 (X    : in     Pair;
                      C    : in     Boolean;
                      N    :    out Natural)
   with Global  => null,
        Depends => (N => X,
                    null => C)
   is
      Obj : constant Pair := X'Update (B => X.B'Update (Round => C));
      Tmp : Widget_T := Widget_T (Obj.B);
   begin
      N := Tmp.Hash;
   end Test_10;

   --  Testing constants
   procedure Test_11 (N : out Natural)
   with Global  => null,
        Depends => (N => null)
   is
      Tmp : Widget_T := Null_Widget;
   begin
      N := Tmp.Hash;
   end Test_11;

   --  Testing derived records
   procedure Test_12 (X : in     Integer;
                      Y :    out Integer)
   with Global  => null,
        Depends => (Y => X)
   is
      type R1 is record
         F : Integer;
      end record;

      type R2 is new R1;

      Tmp1 : R1 := (F => X);
      Tmp2 : R2 := R2 (Tmp1);
   begin
      Y := Tmp2.F;
   end Test_12;

   --  Test assignments (as opposed to declarations). Very much copied from
   --  test 9.
   procedure Test_13 (A, B : in     Integer;
                      C    : in     Boolean;
                      X    :    out Natural;
                      Y    :    out Boolean;
                      Z    :    out Integer)
   with Global  => null,
        Depends => (X => (A, B),
                    Y => C,
                    Z => B)
   is
      Obj  : Nice_Widget_T;
      Tmp  : Pair;
      Tmp2 : Widget_T;
   begin
      Widget_T (Obj) := (X => A,
                         Y => B);
      Obj.Round      := C;
      Tmp.A          := Widget_T (Obj);
      Tmp.B          := Obj;
      Tmp2           := Widget_T (Tmp.B);

      X              := Tmp2.Hash;
      Y              := Tmp.B.Round;
      Z              := Tmp.A.Y;
   end Test_13;

   --  Test for an odd regression relating to arrays.
   procedure Test_14 (X : out Boolean)
   with Global => null
   is
      type Record_With_Mutable_Discrs (Present : Boolean := False) is record
         case Present is
            when True =>
               Field : Natural;
            when False => null;
         end case;
      end record;
      type Mutable_Array is array (Positive range <>) of
        Record_With_Mutable_Discrs;
      A  : Mutable_Array (1 .. 1) := (1 => (Present => False));
   begin
      A (1) := (Present => False);
      X     := A (1).Present;
   end Test_14;

   --  Test for a regression relating to discriminated types.
   procedure Test_15 (X : out Boolean)
   with Global => null
   is
      type Record_With_Mutable_Discrs (Present : Boolean := False) is record
         case Present is
            when True =>
               Field : Natural;
            when False => null;
         end case;
      end record;
      type Holder (Present : Boolean) is record
         Content : Record_With_Mutable_Discrs (Present);
      end record;
      function Id (H : Holder) return Holder is (H);
      H1 : Holder (False);
   begin
      X := Id (H1).Content.Present;
   end Test_15;

   --  Another regression related to discriminated types.
   procedure Test_16 (R : out Boolean)
   with Global => null
   is
      type T (D : Boolean := False) is record
         case D is
            when True =>
               X : Integer;
            when False =>
               null;
         end case;
      end record;
      function F (X : T) return Boolean is (X.D);
      A : T (False) := (D => False);
      B : T;
   begin
      B := A;
      R := F (B);
   end Test_16;

   --  Tests a regression related to private tagged types.
   procedure Test_17 (N : out Integer;
                      M : out Integer)
   with Global  => null,
        Depends => (N => null,
                    M => null)
   is
      type R is record
         Valid : Boolean;
         W     : Magic_Widget_T;
      end record;
      Tmp  : Magic_Widget_T;
      Tmp2 : R;
   begin
      Zero_Widget (Tmp);
      Tmp2 := (Valid => True,
               W     => Tmp);
      N := Tmp2.W.Hash;
      M := Widget_T (Tmp2.W).Hash;
   end Test_17;

   --  Tests a regresstion related to constants and (old) computed globals.
   procedure Test_18 (N : out Integer)
   with Pre => True
   is
      Tmp : Widget_T;
   begin
      Other.New_Widget (Tmp);
      N := Tmp.Hash;
   end Test_18;

   --  Tests a regression relating to types derived from private types.
   procedure Test_19 (A : in     Misc_Private_T;
                      N : in     Integer;
                      B :    out Boolean)
   with Global  => null,
        Depends => (B => (A, N)),
        Pre     => not A.Valid
   is
      type T is new Misc_Private_T (False);
      X : T;
   begin
      X := T (A);
      Modify_It (X, N);
      B := X.Valid;
   end Test_19;

   procedure Test_20 (A : in     Integer;
                      B : in     Boolean;
                      N :    out Natural;
                      M :    out Natural;
                      O :    out Boolean)
   with Global  => null,
        Depends => (N => (A, B),
                    M => A,
                    O => B)
   is
      X : Nice_Widget_T := (X     => A,
                            Y     => A,
                            Round => B);
      Y : Widget_T'Class := Widget_T'Class (X);
      Z : Nice_Widget_T := Nice_Widget_T (Y);    -- !!! missing y'ext
   begin
      N := Y.Hash;
      M := Z.X;
      O := Z.Round;
   end Test_20;

   procedure Test_21 (Obj : in     Root_T;
                      N   :    out Natural)
   with Global  => null,
        Depends => (N => Obj),
        Extensions_Visible
   is
      Tmp : constant Root_T'Class := Obj;
   begin
      N := Tmp.Hash;
   end Test_21;

   procedure Test_22 (A : in     Root_T;
                      N :    out Natural)
   with Global  => null,
        Depends => (N => A),
        Extensions_Visible
   is
      --  B : Root_T'Class := A;
   begin
      Test_21 (A, N);
      --  N := N + B.Hash;
   end Test_22;

   --  This comes from NA15-008
   procedure Test_23 (B : Boolean)
   with Global => null
   is
      type T1 is tagged record
         F : Boolean;
      end record;
      X : T1'Class := T1'(F => B);
   begin
      null;
   end Test_23;

   --  This comes from NA15-008, I guess this kind of thing will be
   --  illegal in SPARK.
   procedure Test_24
   with Global => null
   is
      type T1 is tagged null record;
      type T2 is new T1 with null record;
      X : T1'Class := T1'(null record);
      Y : T2 := T2 (X);
   begin
      null;
   end Test_24;

   --  Extensions are not visible, W and X should look pretty similar.
   procedure Test_25 (A : Integer;
                      W : Widget_T;
                      M : out Integer;
                      N : out Integer)
   with Global => null
   is
      X : Widget_T := (X => A,
                       Y => 0);
   begin
      M := W.Hash;
      N := X.Hash;
   end Test_25;

   procedure Test_26 (A  : Integer;
                      W  : Widget_T;
                      O1 : out Integer;
                      O2 : out Integer;
                      O3 : out Integer;
                      O4 : out Integer;
                      O5 : out Integer)
   with Global => null,
        Depends => (O1 => null,
                    O2 => null,
                    O3 => W,
                    O4 => W,
                    O5 => (W, A)),
        Extensions_Visible
   is
      --  X is here so that we can see that it doesn't contain any
      --  extensions.
      X  : Widget_T := (X => A,
                        Y => 0);
      pragma Warnings (Off, "initialization has no effect");
      Y  : Widget_T       := W;
      pragma Warnings (On, "initialization has no effect");
      Z  : Widget_T'Class := W'Update (X => 0);

      ZZ : Widget_T'Class := Widget_T'Class (W);
   begin
      X.X := 0;
      O1 := X.Hash;   -- does not depend on A

      Y.X := 0;
      Y.Y := 0;
      O2 := Y.Hash;   -- does not depend on W

      Z.X := 0;
      O3 := Z.Hash;   -- depends on W

      ZZ.X := 0;
      ZZ.Y := 0;
      O4 := ZZ.Hash;  -- depends on W

      O5 := Widget_T'Class (W'Update (X => 0, Y => A)).Hash;
      -- 'update does not lose the extensions
   end Test_26;

   procedure Test_27 (W  : in out Widget_T;
                      O1 :    out Boolean;
                      O2 :    out Boolean;
                      O3 :    out Boolean)
   with Global => null,
        Depends => (W  => W,
                    O1 => null,
                    O2 => W,
                    O3 => W),
        Extensions_Visible
   is
   begin
      W.X := 0;
      W.Y := 0;

      O1 := F_Get_Item   (W);
      O2 := F_Get_Item_C (W);
      O3 := F_Get_Item_E (W);
   end Test_27;

   procedure Test_28 (W  : in out Widget_T;
                      O1 :    out Boolean;
                      O2 :    out Boolean;
                      O3 :    out Boolean)
   with Global => null,
        Depends => (W  => W,
                    O1 => null,
                    O2 => W,
                    O3 => W),
        Extensions_Visible
   is
   begin
      W.X := 0;
      W.Y := 0;

      P_Get_Item   (W, O1);
      P_Get_Item_C (W, O2);
      P_Get_Item_E (W, O3);
   end Test_28;

   procedure Test_29 (W : in out Widget_T;
                      A : Integer;
                      B : Integer;
                      C : Integer)
   with Global => null,
        Extensions_Visible
   is
   begin
      W.X := 0;
      W.Y := 0;

      P_Mod_Item   (W, A);
      P_Mod_Item_C (W, B);
      P_Mod_Item_E (W, C);
   end Test_29;

   procedure Test_30 (A  : in out Widget_T;
                      Nw :        Nice_Widget_T;
                      B  : in out Pair;
                      C  : in     Pair;
                      D  : in out Widget_T;
                      E  :    out Widget_T;
                      F  :    out Widget_T;
                      G  :    out Widget_T;
                      H  :    out Widget_T)
   with Global => null,
        Extensions_Visible
   is
   begin
      B.A                := A;
      Widget_T (B.B)     := A;
      A                  := C.A;
      Widget_T (D)       := C.A;
      Widget_T'Class (E) := Widget_T'Class (C.A);
      Widget_T'Class (F) := Widget_T'Class (A);
      Widget_T'Class (G) := Widget_T'Class (C.B);
      Widget_T'Class (H) := Widget_T'Class (Nw);
   end Test_30;

   procedure Test_31 (W1 :        Widget_T;
                      W2 :    out Widget_T;
                      O1 :    out Integer)
   with Global => null,
        Extensions_Visible
   is
      procedure Test_31_In
      with Global => (Input  => W1,
                      Output => O1)
      is
         Tmp : Widget_T'Class := W1;
      begin
         O1 := Tmp.Hash;
      end Test_31_In;

      procedure Test_31_Out
      with Global => (Input  => W1,
                      Output => W2)
      is
      begin
         Widget_T'Class (W2) := Widget_T'Class (W1);
      end Test_31_Out;
   begin
      Test_31_In;
      Test_31_Out;
   end Test_31;

end Tests;
