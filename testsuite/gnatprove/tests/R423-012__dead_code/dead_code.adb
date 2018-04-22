package body Dead_Code
  with SPARK_Mode
is
   function For_Loop1 (X : Integer) return Integer is
   begin
      for J in 1 .. X loop
         return J;
      end loop;
      return 0;
   end For_Loop1;

   function For_Loop2 (X : Positive) return Integer is
   begin
      for J in 1 .. X loop
         return J;
      end loop;
      pragma Assert (False);
      return 0;
   end For_Loop2;

   function For_Loop3 (X : Positive) return Integer is
   begin
      for J in 1 .. X loop
         return J;
      end loop;
      raise Program_Error;
   end For_Loop3;

   function For_Loop4 (X : Positive) return Integer is
   begin
      for J in 1 .. X loop
         return J;
      end loop;
      return 0;
   end For_Loop4;

   function While_Loop1 (X : Integer) return Integer is
      J : Integer := 1;
   begin
      while J in 1 .. X loop
         return J;
      end loop;
      return 0;
   end While_Loop1;

   function While_Loop2 (X : Positive) return Integer is
      J : Integer := 1;
   begin
      while J in 1 .. X loop
         return J;
      end loop;
      pragma Assert (False);
      return 0;
   end While_Loop2;

   function While_Loop3 (X : Positive) return Integer is
      J : Integer := 1;
   begin
      while J in 1 .. X loop
         return J;
      end loop;
      raise Program_Error;
   end While_Loop3;

   function While_Loop4 (X : Positive) return Integer is
      J : Integer := 1;
   begin
      while J in 1 .. X loop
         return J;
      end loop;
      return 0;
   end While_Loop4;

   function Plain_Loop1 (X : Integer) return Integer is
      J : Integer := 1;
   begin
      loop
         exit when X > 1 and X < 1;
         return J;
      end loop;
      return 0;
   end Plain_Loop1;

   function Plain_Loop2 (X : Positive) return Integer is
      J : Integer := 1;
   begin
      loop
         exit when X > 1 and X < 1;
         return J;
      end loop;
      pragma Assert (False);
      return 0;
   end Plain_Loop2;

   function Plain_Loop3 (X : Positive) return Integer is
      J : Integer := 1;
   begin
      loop
         exit when X > 1 and X < 1;
         return J;
      end loop;
      raise Program_Error;
   end Plain_Loop3;

   function Plain_Loop4 (X : Positive) return Integer is
      J : Integer := 1;
   begin
      loop
         exit when X > 1 and X < 1;
         return J;
      end loop;
      return 0;
   end Plain_Loop4;

end Dead_Code;
