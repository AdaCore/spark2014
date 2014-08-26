with Foo; use Foo;

package body Tests is

   procedure Test_01 (Obj : in     Root_T;
                      N   :    out Natural)
   with Global  => null,
        Depends => (N => null)
   is
   begin
      N := Obj.Hash;
   end Test_01;

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

end Tests;
