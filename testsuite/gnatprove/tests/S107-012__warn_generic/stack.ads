
--  pragma SPARK_Mode;
--pragma Pure; -- req 0

generic
   type T is private;
   Default_Value : T;
package Stack with SPARK_Mode => On is




   -- Requirements:
   -- 0 This package shall not contain any data
   -- 1 After creation, the stack shall have size = 0
   -- 2 The stack shall have a maximum size, Max_Size
   -- 3 Adding an element shall only be possible when Size < Max_Size
   -- 4 Each time an element is added, Size shall be incremented by 1
   -- 5 Each time an element is removed, Size shall be decremented by 1
   -- 6 The element added shall be put at the top of the stack
   -- 7 Adding an element shall not affect elements already added
   -- 8 Removing an element shall only be possible when Size > 0
   -- 9 Removing an element shall return the element at the top
   -- 10 Removing an element shall not affect the other elements

   Max_Size : constant Natural := 10;

   type Index_Type is range 0..Max_Size;
   type Buffer_Array is array(Index_Type) of T;

   type Stack_Type is record
      Top  : Index_Type := 0;
      Data : Buffer_Array;
   end record;

   function Size (Stack : Stack_Type) return Index_Type;

   function Construct return Stack_Type with
     Post => Size (Construct'Result) = 0; -- req 1

end Stack;

