with Foo; use Foo;

package body Tests is

   type Pair is record
      A : Widget_T;
      B : Nice_Widget_T;
   end record;

   --  All annotations are meant to be `correct', so this test should not
   --  produce any messages.

   --  procedure Test_01 (Obj : in     Root_T;
   --                     N   :    out Natural)
   --  with Global  => null,
   --       Depends => (N => null)
   --  is
   --  begin
   --     N := Obj.Hash;
   --  end Test_01;

   --  procedure Test_02 (Obj : in     Widget_T;
   --                     N   :    out Natural)
   --  with Global  => null,
   --       Depends => (N => Obj)
   --  is
   --  begin
   --     N := Obj.Hash;
   --  end Test_02;

   --  procedure Test_03 (Obj : in     Root_T'Class;
   --                     N   :    out Natural)
   --  with Global  => null,
   --       Depends => (N => Obj)
   --  is
   --  begin
   --     N := Obj.Hash;
   --  end Test_03;

   --  procedure Test_04 (Obj : in     Widget_T'Class;
   --                     N   :    out Natural)
   --  with Global  => null,
   --       Depends => (N => Obj)
   --  is
   --  begin
   --     N := Obj.Hash;
   --  end Test_04;

   --  --  View conversions.
   --  procedure Test_05 (A, B : in     Integer;
   --                     C    : in     Boolean;
   --                     N    :    out Natural)
   --  with Global  => null,
   --       Depends => (N => (A, B),
   --                   null => C)
   --  is
   --     Obj : constant Nice_Widget_T := (X     => A,
   --                                      Y     => B,
   --                                      Round => C);
   --     Tmp : Widget_T := Widget_T (Obj);
   --  begin
   --     N := Tmp.Hash;
   --  end Test_05;

   --  procedure Test_06 (A, B : in     Integer;
   --                     C    : in     Boolean;
   --                     N    :    out Natural)
   --  with Global  => null,
   --       Depends => (N => (A, B),
   --                   null => C)
   --  is
   --     Obj : constant Nice_Widget_T := (X     => A,
   --                                      Y     => B,
   --                                      Round => C);
   --  begin
   --     N := Widget_T (Obj).Hash;
   --  end Test_06;

   --  procedure Test_07 (A, B : in     Integer;
   --                     C    : in     Boolean;
   --                     N    :    out Natural)
   --  with Global  => null,
   --       Depends => (N => C,
   --                   null => (A, B))
   --  is
   --     Obj : Nice_Widget_T := (X     => A,
   --                             Y     => B,
   --                             Round => C);
   --  begin
   --     --  Clear X and Y
   --     Zero_Widget (Widget_T (Obj));
   --     N := Obj.Hash;
   --  end Test_07;

   --  procedure Test_08 (A, B : in     Integer;
   --                     C    : in     Boolean;
   --                     N    :    out Natural)
   --  with Global  => null,
   --       Depends => (N    => null,
   --                   null => (A, B, C))
   --  is
   --     Obj : Nice_Widget_T := (X     => A,
   --                             Y     => B,
   --                             Round => C);
   --  begin
   --     --  Clear everything
   --     Zero_Widget (Obj);
   --     N := Obj.Hash;
   --  end Test_08;

   --  --  Test view conversions of record fields.
   --  procedure Test_09 (A, B : in     Integer;
   --                     C    : in     Boolean;
   --                     N    :    out Natural)
   --  with Global  => null,
   --       Depends => (N => (A, B),
   --                   null => C)
   --  is
   --     Obj : constant Nice_Widget_T := (X     => A,
   --                                      Y     => B,
   --                                      Round => C);
   --     Tmp : Pair := (A => Widget_T (Obj),
   --                    B => Obj);
   --     Tmp2 : Widget_T := Widget_T (Tmp.B);
   --  begin
   --     N := Tmp2.Hash;
   --  end Test_09;

   --  --  Testing update attributes
   --  procedure Test_10 (X    : in     Pair;
   --                     C    : in     Boolean;
   --                     N    :    out Natural)
   --  with Global  => null,
   --       Depends => (N => X,
   --                   null => C)
   --  is
   --     Obj : constant Pair := X'Update (B => X.B'Update (Round => C));
   --     Tmp : Widget_T := Widget_T (Obj.B);
   --  begin
   --     N := Tmp.Hash;
   --  end Test_10;

   --  --  Testing constants
   --  procedure Test_11 (N : out Natural)
   --  with Global  => null,
   --       Depends => (N => null)
   --  is
   --     Tmp : Widget_T := Null_Widget;
   --  begin
   --     N := Tmp.Hash;
   --  end Test_11;

   --  --  Testing derived records
   --  procedure Test_12 (X : in     Integer;
   --                     Y :    out Integer)
   --  with Global  => null,
   --       Depends => (Y => X)
   --  is
   --     type R1 is record
   --        F : Integer;
   --     end record;

   --     type R2 is new R1;

   --     Tmp1 : R1 := (F => X);
   --     Tmp2 : R2 := R2 (Tmp1);
   --  begin
   --     Y := Tmp2.F;
   --  end Test_12;

   --  --  Test assignments (as opposed to declarations). Very much copied from
   --  --  similar from test 9.
   --  procedure Test_13 (A, B : in     Integer;
   --                     C    : in     Boolean;
   --                     X    :    out Natural;
   --                     Y    :    out Boolean;
   --                     Z    :    out Integer)
   --  with Global  => null,
   --       Depends => (X => (A, B),
   --                   Y => C,
   --                   Z => B)
   --  is
   --     Obj  : Nice_Widget_T;
   --     Tmp  : Pair;
   --     Tmp2 : Widget_T;
   --  begin
   --     Widget_T (Obj) := (X => A,
   --                        Y => B);
   --     Obj.Round      := C;
   --     Tmp.A          := Widget_T (Obj);
   --     Tmp.B          := Obj;
   --     Tmp2           := Widget_T (Tmp.B);

   --     X              := Tmp2.Hash;
   --     Y              := Tmp.B.Round;
   --     Z              := Tmp.A.Y;
   --  end Test_13;

   --  --  Test for an odd regression relating to arrays.
   --  procedure Test_14 (X : out Boolean)
   --  with Global => null
   --  is
   --     type Record_With_Mutable_Discrs (Present : Boolean := False) is record
   --        case Present is
   --           when True =>
   --              Field : Natural;
   --           when False => null;
   --        end case;
   --     end record;
   --     type Mutable_Array is array (Positive range <>) of
   --       Record_With_Mutable_Discrs;
   --     A  : Mutable_Array (1 .. 1) := (1 => (Present => False));
   --  begin
   --     A (1) := (Present => False);
   --     X     := A (1).Present;
   --  end Test_14;

   --  --  Test for a regression relating to discriminated types.
   --  procedure Test_15 (X : out Boolean)
   --  is
   --     type Record_With_Mutable_Discrs (Present : Boolean := False) is record
   --        case Present is
   --           when True =>
   --              Field : Natural;
   --           when False => null;
   --        end case;
   --     end record;
   --     type Holder (Present : Boolean) is record
   --        Content : Record_With_Mutable_Discrs (Present);
   --     end record;
   --     function Id (H : Holder) return Holder is (H);
   --     H1 : Holder (False);
   --  begin
   --     X := Id (H1).Content.Present;
   --  end Test_15;

   --  Another regression related to discriminated types.
   procedure Test_16 (R : out Boolean)
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

end Tests;
