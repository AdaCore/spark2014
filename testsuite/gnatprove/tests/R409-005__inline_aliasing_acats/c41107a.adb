PROCEDURE C41107A IS

     C : STRING (1..7) := "ABCDEFG";

     V3 : INTEGER := 3;

     PROCEDURE P2 (Y : IN OUT CHARACTER;
                   Z : OUT CHARACTER) IS
     BEGIN
        null;
     END P2;

BEGIN
     P2 (C(3..6)(V3*2), C(3..6)(3));
END C41107A;
