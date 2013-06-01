PROCEDURE C45532O IS

     FULL_SCALE      : CONSTANT := 2 ** (48 - 1);
     RNG1            : CONSTANT := FULL_SCALE * 0.5;
     TYPE FX_0P5  IS DELTA 0.5 RANGE -RNG1 * 1 .. RNG1 * 1 - 0.5;
     TYPE FX_1    IS DELTA 1.0 RANGE -RNG1 * 2 .. RNG1 * 2 - 1.0;
     TYPE FX_RNG1 IS DELTA RNG1
                    RANGE -RNG1 * FULL_SCALE .. RNG1 * (FULL_SCALE - 1);

     A              : FX_0P5  := 0.0;
     B              : FX_1    := 0.0;
     RESULT_VALUE   : FX_RNG1 := 0.0;
BEGIN
     RESULT_VALUE := FX_RNG1 (A * B);

END C45532O;
