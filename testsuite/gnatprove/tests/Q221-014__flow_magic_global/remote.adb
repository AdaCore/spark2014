package body Remote is

   Hidden : Integer := 0;

   function Read_Hidden_Global return Integer is (Hidden);

   Const : constant Integer := Hidden;

   function Read_Hidden_Const return Integer is (Const);

end;
