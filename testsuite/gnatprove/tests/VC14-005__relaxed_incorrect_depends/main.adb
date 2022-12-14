procedure Main
  with
    SPARK_Mode => On
is

   H : Integer := 12 with Relaxed_Initialization;

   procedure Write_H_V1 (B : Boolean) with
     Global => (Output => H)
   is
   begin
      if B then
         H := 15;
      end if;
   end Write_H_V1;

   procedure Bad_Depends_V1 (X : Integer; Y : out Integer) with
     Global => (In_Out => H),
     Depends => ((H, Y) => null, null => (H, X))
   is
   begin
      H := X;
      Write_H_V1 (False);
      Y := H;
      H := 0;
   end Bad_Depends_V1;

   procedure Write_H_V2 (B : Boolean) with
     Global => (Output => H),
     Post => H'Initialized
   is
   begin
      if B then
         H := 15;
      end if;
   end Write_H_V2;

   procedure Bad_Depends_V2 (X : Integer; Y : out Integer) with
     Global => (In_Out => H),
     Depends => ((H, Y) => null, null => (H, X))
   is
   begin
      H := X;
      Write_H_V2 (False);
      Y := H;
      H := 0;
   end Bad_Depends_V2;

begin
   null;
end Main;
