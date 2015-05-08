package body Other is
   function Gimme_C return Integer is (C);

   function Gimme_V_Plus_C return Integer is (V + C);

   function Gimme_Zero return Integer is (0);

   function Identity (X : Integer) return Integer is (X);
end Other;
