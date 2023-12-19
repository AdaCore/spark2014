package body Through_Model with SPARK_Mode is

   procedure Add (L : in out List; E : Integer) is
   begin
      L := new List_Cell'(E, L);
   end Add;

end Through_Model;
