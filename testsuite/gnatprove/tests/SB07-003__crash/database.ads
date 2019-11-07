package Database with SPARK_Mode is

   type Email_Address_Type is new String;

   type Email_Access is access Email_Address_Type;
   function Query_Email (Email : Email_Address_Type) return Integer;

end Database;
