package body Dir is

   function Normalize_Pathname
     (Name           : String;
      Directory      : String  := "";
      Resolve_Links  : Boolean := True) return String;

   function Normalize_Pathname
     (Name           : String;
      Directory      : String  := "";
      Resolve_Links  : Boolean := True) return String is
   begin
      return Name;
   end Normalize_Pathname;

   function Test
     (Name           : String;
      Directory      : String  := "") return String is
   begin
      return Name;
   end Test;

   function Is_Valid (Name : String) return Boolean is (True);
   function Full_Name (Name : String) return String is
   begin
      if not Is_Valid (Name) then
         return Name;

      else
         declare
            Value : constant String := Normalize_Pathname (Name);
            Test_Value : constant String := Test (Name);
            subtype Result is String (1 .. Value'Length);

         begin
            return Result (Value);
         end;
      end if;
   end Full_Name;

end Dir;
