package Test is

   type String_Pointer is access String;

   type Container is private;

   procedure Init (C : out Container; Value : in out String_Pointer) with Depends => (Value => null, C => Value), Post => Value = null;

   function Init_Test return Container with Volatile_Function;

private

   type Container is
      record
         Elem : String_Pointer;
      end record;

end Test;
