package body Update_Equality with SPARK_Mode is
   procedure Partial (X : in out A) is
   begin
      X (1) := 0;
   end Partial;

   procedure Reversed_Delta (X : in out A) is
   begin
      X (1) := 0;
   end Reversed_Delta;

   procedure Old_Partial (X : in out A) is
   begin
      X := (others => 0);
   end Old_Partial;

   procedure Initialized (X : in out A) is
   begin
      X (1) := 0;
   end Initialized;

   procedure Replace_All (X : in out A) is
   begin
      X := (others => 0);
   end Replace_All;

   procedure Object_Relaxed (X : in out Plain_Array) is
   begin
      X (1) := 0;
   end Object_Relaxed;

   procedure Custom_Equality (X : in out Records) is
   begin
      X (1) := (F => 0);
   end Custom_Equality;
end Update_Equality;
