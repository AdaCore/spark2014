pragma Ada_2012;

with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

package Memory is

   Max_Address : constant := 10_000;

   --  Basic type returned by allocation: a chunk of memory

   type Chunk is private;

   Null_Chunk : constant Chunk;

   function Size (C : Chunk) return Natural;

   --  Model of memory allocation

   subtype Model_Address is Natural;
   package Lists is new Formal_Doubly_Linked_Lists (Model_Address);
   use Lists;
   subtype Model_Free_List is List (Max_Address);
   function Model_F return Model_Free_List;

   --  API of memory allocation

   function Alloc (Size : Positive) return Chunk
     with Post => (if Alloc'Result /= Null_Chunk then
                     Model_F.Length = Model_F.Length'Old - Count_Type (Size));

   procedure Free (C : Chunk)
     with Post => Model_F.Length = Model_F.Length'Old + Count_Type (Size (C));

private

   subtype Address is Natural range 0 .. Max_Address;

   type Chunk is record
     Addr : Address;
     Size : Natural;
   end record;

   Null_Address : constant Address := 0;

   Null_Chunk : constant Chunk := Chunk'(Addr => Null_Address, Size => 0);

   function Size (C : Chunk) return Natural is (C.Size);

   subtype Valid_Address is Address range 1 .. Max_Address;

   function Model_A (A : Address) return Model_Address is
      (Model_Address (A));

end Memory;
