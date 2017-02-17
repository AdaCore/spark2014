package body Sub is pragma SPARK_Mode (On);

   function Incorrect (X : S) return S is
   begin
      -- This will fail when X / 2 is not even
      return (X / 2);
   end Incorrect;

   function F (X : S) return S is
      -- This is OK because we use the subtype without predicate
      Tmp : constant My_Int := X / 2;
   begin
      if Tmp mod 2 = 0 then
         return Tmp;
      else
         return Tmp + 1;
      end if;
   end F;

   procedure Divide (X : in out S) is
   begin
      -- This will fail when X / 2 is not even
      X := X / 2;
      if not (X mod 2 = 0) then
         X := X + 1;
      end if;
   end Divide;

   procedure Divide_T (X : in out T) is
   begin
      -- The subtype predicate is not checked on X when we change Global
      if not (X / 2 mod 2 = 0) then
         Global := 1;
      else
         Global := 0;
      end if;

      -- This is OK because we have set Global accordingly
      X := X / 2;

      -- We increase Global, this breaks the predicate on procedure Exit, and
      -- the check that is done on out parameters will fail
      Global := Global + 1;
   end Divide_T;
end Sub;
