with Bad_Funcs; use Bad_Funcs;

procedure Use_Bads with SPARK_Mode is
begin
   pragma Assert (Bad);
   Bad_Funcs.G := 0;
end Use_Bads;
