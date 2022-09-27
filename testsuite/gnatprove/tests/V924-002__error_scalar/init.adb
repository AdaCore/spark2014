with Core; use Core;

procedure init (X : out Rec) with SPARK_Mode is
begin
   X := (Comp => (others => 0));
end init;
