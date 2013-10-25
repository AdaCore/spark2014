procedure Foo is

   PACKAGE P IS

      TYPE T IS PRIVATE;

   PRIVATE

      TYPE T IS ('Z', X);

   END P;

   VT : P.T;

   PACKAGE BODY P IS
   BEGIN

      VT := 'Z';

      CASE VT IS
         WHEN X => null;
         WHEN 'Z' => NULL; -- OK
      END CASE;

   END P;

begin

   null;

end Foo;