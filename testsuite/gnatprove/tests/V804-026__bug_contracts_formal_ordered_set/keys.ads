with Sets; use Sets;
package Keys with SPARK_Mode is
   function Key (X : Natural) return Natural is (X);
   package Keys_Pack is new Sets_Pack.Generic_Keys (Natural, Key);
end Keys;
