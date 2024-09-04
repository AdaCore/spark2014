pragma Extensions_Allowed (All_Extensions);

procedure Foo with SPARK_Mode is
   C : String with External_Initialization => "foo.txt";
begin
   null;
end Foo;
