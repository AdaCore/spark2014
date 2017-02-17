package Hello
with
  Spark_Mode => On
is

   type Language_Level is (Formal, Casual);

   procedure Set_Language_Level (Level : Language_Level);

   procedure Say_Hello
     (Who : in String);
   --  Implements req_01_hello, req_02_who and req_03_formal_casual
   --  Prints a hello message on stdout.

end Hello;
