with Foo; use Foo;

package body Tests is

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

end Tests;
