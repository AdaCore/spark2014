PROCEDURE C41107A IS

     C : STRING (1..7) := "ABCDEFG";

     V : INTEGER := 3;

     PROCEDURE P (X : IN OUT CHARACTER;
                  Y :    OUT CHARACTER) IS
     BEGIN
        null;
     END P;

BEGIN
     P (C(3..6)(V), C(3..6)(3));
END C41107A;
