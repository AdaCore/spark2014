procedure Main (L, H : Integer) is
   type T is array (Integer range <>) of Integer;
   type R (LD, HD : Integer) is record
      C : T (LD .. HD);
   end record;
   --  A record type whose component is a dynamic-size array

   X : R (L, H) := (LD => L, HD => H, C => (others => 0));
   Y : R (L, H);
   --  A dummy "input" and "output" record objects

   procedure Inner (X : R) with Pre => True is
   begin
      for J in X.C'Range loop
         --  The "X.C'Range" above is expanded into "X.C'First .. X.C'Last",
         --  but only when X is a formal parameter (possibly of mode IN);
         --  when it is a object (even a constant), frontend introduces
         --  temporary objects initialized with "X.C'First" and "X.C'Last",
         --  respectively, and uses them as bounds of the FOR loop.

         Y.C (J) := 0;
      end loop;
   end Inner;

begin
   Inner (X);
end;
