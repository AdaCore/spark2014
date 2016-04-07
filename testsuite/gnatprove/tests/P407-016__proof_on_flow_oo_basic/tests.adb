with Foo; use Foo;

package body Tests is

   pragma Warnings (Off, "subprogram * has no effect");
   pragma Warnings (Off, "analyzing unreferenced *");

   type Pair is record
      A : Widget_T;
      B : Nice_Widget_T;
   end record;

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

end Tests;
