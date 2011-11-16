PROCEDURE C74305A IS

     PACKAGE PK IS
          TYPE T2 IS PRIVATE;

     PRIVATE

          TYPE T2 IS ARRAY (1..2) OF INTEGER; -- OK.

          C2 : CONSTANT T2 := (1,1);          -- OK.
     END PK;

BEGIN
   null;
END C74305A;
