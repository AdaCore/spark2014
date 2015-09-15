package Hide_Access with SPARK_Mode is
   subtype Letter is Character range 'a' .. 'z';
   type String_Access is private;
   function New_String_Access (W : String) return String_Access;
   type Dictionary is array (Letter) of String_Access;
   procedure Store (D : in out Dictionary; W : String);

private
   pragma SPARK_Mode (Off);
   type String_Access is access String;
   function New_String_Access (W : String) return String_Access is
      (new String'(W));
end Hide_Access;
