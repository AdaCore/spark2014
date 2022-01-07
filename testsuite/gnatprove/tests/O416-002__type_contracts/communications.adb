package body Communications
  with SPARK_Mode
is
   procedure Mark_Duplicates (Com : in out Communication) is
      Null_Msg : constant Message := (Sent => "2012-01-01", Received => "2012-01-01");
   begin
      Com.Msgs := (others => Null_Msg);
   end Mark_Duplicates;

   function Create (A : Message_Arr) return Communication is
      Coms : Communication (A'Length);
   begin
      Coms.Msgs := A;
      return Coms;
   end Create;

end Communications;
