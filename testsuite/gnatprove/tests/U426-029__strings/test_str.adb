procedure Test_Str with SPARK_Mode is
   subtype idx is Integer range 0 .. Natural'Last - 2;
   type StringBase is array (idx range <>) of Character
     with Predicate => StringBase'Last in -1 .. idx'Last
     and then StringBase'First in 0 .. StringBase'Last + 1;

   subtype String0 is StringBase
     with Predicate => String0'First = 0;
   type StringPtr is not null access String0;

   type ValueKind is (StringKind, OtherKind);

   type Value (K : ValueKind) is record
      case K is
      when StringKind => StringVal : StringPtr;
      when OtherKind => null;
      end case;
   end record;

   function F (X : String0) return Boolean with Import;

   function Get_String (V : Value) return String0 is
     (case V.K is
         when StringKind => V.StringVal.all,
         when OtherKind  => (0..-1 => ' '));

   procedure Do_Something (V : Value) is
   begin
      declare
         S : String0 := Get_String (V);
      begin
         pragma Assert (F (S) = F (Get_String (V)));
      end;
   end Do_Something;
begin
   null;
end Test_Str;
