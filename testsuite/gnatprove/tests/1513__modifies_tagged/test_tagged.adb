procedure Test_Tagged with SPARK_Mode is
   package Operations is
      type T is tagged record
         F, G : Integer;
      end record;

      procedure Update (X : in out T) with
        Modifies => X.F;

      procedure Update_With_Class_Post (X : in out T) with
        Modifies => X.F,
        Post'Class => X.F = 0;
   end Operations;

   package body Operations is
      procedure Update (X : in out T) is
      begin
         X.F := 0;
      end Update;

      procedure Update_With_Class_Post (X : in out T) is
      begin
         X.F := 0;
      end Update_With_Class_Post;
   end Operations;

   --  Static calls preserve Modifies when no specific postcondition is given

   procedure Check_Tagged (X : in out Operations.T) with
     Post => X.G = X.G'Old
   is
   begin
      Operations.Update (X);
   end Check_Tagged;

   --  The class-wide postcondition is also retained

   procedure Check_Class_Post (X : in out Operations.T) with
     Post => X.F = 0 and X.G = X.G'Old
   is
   begin
      Operations.Update_With_Class_Post (X);
   end Check_Class_Post;
begin
   null;
end Test_Tagged;
