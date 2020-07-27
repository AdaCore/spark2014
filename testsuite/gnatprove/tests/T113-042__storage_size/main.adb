with Ada.Unchecked_Deallocation;

procedure Main is
   type T is null record;
   function Zero return Integer is (0);
   type Ptr is access T with Storage_Size => Zero;
   --  An access type with whose Storage_Size is non-static but zero

   type Ptr2 is access T with Storage_Pool => Ptr'Storage_Pool;
   --  An access type with Storage_Pool

   function Dummy return T with Pre => True is
      D : T;
   begin
      return D;
   end;

   X : Ptr := new T'(Dummy);

   procedure Free is new Ada.Unchecked_Deallocation (T, Ptr);

begin
   pragma Assert (X /= null);
   Free (X); --  This call raises an exception at runtime
end;
