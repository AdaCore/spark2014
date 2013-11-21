package body AR is

  -----------------------------------------------
  -- [A] Simple one-dimensional arrays
  -----------------------------------------------
  procedure TestA01
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
  begin
    A(I) := E;
  end TestA01;

  procedure TestA02
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
  begin
    A(I) := E;
  end TestA02;

  procedure TestA03
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
  begin
    A(I) := E;
  end TestA03;

  procedure TestA04
	    (A: in out Arr1T; I, J: in IT1; E, F: in ET1)
  is
  begin
    A(I) := E;
    A(J) := F;
  end TestA04;

  procedure TestA05
	    (A: in out Arr1T; I, J: in IT1; E, F: in ET1)
  is
  begin
    A(I) := E;
    A(J) := F;
  end TestA05;

  procedure TestA06
	    (A: in out Arr1T; I, J: in IT1; E, F: in ET1)
  is
  begin
    A(I) := E;
    A(J) := F;
  end TestA06;

  procedure TestA07
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
    J: IT1;
    F: ET1;
  begin
    A(I) := E;
    if I=IT1'Last then
      J := IT1'First;
    else
      J := I + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J) := F;
  end TestA07;

  procedure TestA08
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
    J: IT1;
    F: ET1;
  begin
    A(I) := E;
    if I=IT1'Last then
      J := IT1'First;
    else
      J := I + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J) := F;
  end TestA08;

  procedure TestA09
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
    J: IT1;
    F: ET1;
    T: Arr1T;
  begin
    T := A;
    A(I) := E;
    pragma Assert_And_Cut (A = T'Update (I => E));
    if I=IT1'Last then
      J := IT1'First;
    else
      J := I + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J) := F;
  end TestA09;

  procedure TestA10
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
    J: IT1;
    F: ET1;
    T: Arr1T;
  begin
    T := A;
    A(I) := E;
    pragma Assert_And_Cut (A = T'Update (I => E));
    if I=IT1'Last then
      J := IT1'First;
    else
      J := I + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J) := F;
  end TestA10;

  procedure TestA11
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
    J: IT1;
    F: ET1;
    T: Arr1T;
  begin
    T := A;
    A(I) := E;
    if I=IT1'Last then
      J := IT1'First;
    else
      J := I + 1;
    end if;
    pragma Assert_And_Cut (A = T'Update (I => E) and ((I=IT1'Last and J=IT1'First) or (I<IT1'Last and J=I+1)) and J in IT1);
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J) := F;
  end TestA11;

  procedure TestA12
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
    J: IT1;
    F: ET1;
    T: Arr1T;
  begin
    T := A;
    A(I) := E;
    if I=IT1'Last then
      J := IT1'First;
    else
      J := I + 1;
    end if;
    pragma Assert_And_Cut (A = T'Update (I => E) and ((I=IT1'Last and J=IT1'First) or (I<IT1'Last and J=I+1)) and J in IT1);
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J) := F;
  end TestA12;

  procedure TestA13
	    (A: in out Arr1T; I: in IT1; E: in ET1)
  is
  begin
    A(I) := E;
  end TestA13;

  procedure TestA14
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
  end TestA14;

  procedure TestA15
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
  end TestA15;

  procedure TestA16
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(5) := 25;
  end TestA16;

  procedure TestA17
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(5) := 25;
  end TestA17;

  procedure TestA18
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(5) := 25;
  end TestA18;

  procedure TestA19
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(5) := B(4);
    A(3) := A(6);
    A(6) := 0;
    A(7) := A(6);
    A(4) := A(5) - A(4);
    A(5) := 0;
    A(10) := 0;
    A(9) := 0;
    A(1) := B(2) - A(2);
    A(2) := 0;
    A(3) := A(3) - B(6);
    A(8) := 0;
  end TestA19;

  procedure TestA20
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(5) := B(4);
    A(3) := A(6);
    A(6) := 0;
    A(7) := A(6);
    A(4) := A(5) - A(4);
    A(5) := 0;
    A(10) := 0;
    A(9) := 0;
    A(1) := B(2) - A(2);
    A(2) := 0;
    A(3) := A(3) - B(6);
    A(8) := 0;
  end TestA20;

  procedure TestA21
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(5) := B(4);
    A(3) := A(6);
    A(6) := 0;
    A(7) := A(6);
    A(4) := A(5) - A(4);
    A(5) := 0;
    A(10) := 0;
    A(9) := 0;
    A(1) := B(2) - A(2);
    A(2) := 0;
    A(3) := A(3) - B(6);
    A(8) := 0;
  end TestA21;

  procedure TestA22
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(5) := B(4);
    A(3) := A(6);
    A(6) := 0;
    A(7) := A(6);
    A(4) := A(5) - A(4);
    A(5) := 0;
    A(10) := 0;
    A(9) := 0;
    A(1) := B(2) - A(2);
    A(2) := 0;
    A(3) := A(3) - B(6);
    A(8) := 0;
  end TestA22;

  procedure TestA23
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(10) := A(1);
    A(9) := A(2);
    A(8) := A(3);
    A(7) := A(4);
    A(1) := B(10);
    A(2) := B(9);
    A(3) := B(8);
    A(4) := B(7);
    A(6) := A(5);
    A(5) := B(6);
  end TestA23;

  procedure TestA24
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(10) := A(1);
    A(9) := A(2);
    A(8) := A(3);
    A(7) := A(4);
    A(1) := B(10);
    A(2) := B(9);
    A(3) := B(8);
    A(4) := B(7);
    A(6) := A(5);
    A(5) := B(6);
  end TestA24;

  procedure TestA25
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(10) := A(1);
    A(9) := A(2);
    A(8) := A(3);
    A(7) := A(4);
    A(1) := B(10);
    A(2) := B(9);
    A(3) := B(8);
    A(4) := B(7);
    A(6) := A(5);
    A(5) := B(6);
  end TestA25;

  procedure TestA26
	    (A: out Arr1T; B: in Arr1T)
  is
  begin
    A := B;
    A(10) := A(1);
    A(9) := A(2);
    A(8) := A(3);
    A(7) := A(4);
    A(1) := B(10);
    A(2) := B(9);
    A(3) := B(8);
    A(4) := B(7);
    A(6) := A(5);
    A(5) := B(6);
  end TestA26;

  -----------------------------------------------
  -- [B] Array of array tests
  -----------------------------------------------
  procedure TestB01
	    (A: in out Arr2T; I1: in IT1; I2: in IT2; E: in ET1)
  is
  begin
    A(I2)(I1) := E;
  end TestB01;

  procedure TestB02
	    (A: in out Arr2T; I1: in IT1; I2: in IT2; E: in ET1)
  is
  begin
    A(I2)(I1) := E;
  end TestB02;

  procedure TestB03
	    (A: in out Arr2T; I1: in IT1; I2: in IT2; E: in ET1)
  is
  begin
    A(I2)(I1) := E;
  end TestB03;

  procedure TestB04
	    (A: in out Arr2T; I1, I2: in IT1; J1, J2: IT2; E, F: in ET1)
  is
  begin
    A(J1)(I1) := E;
    A(J2)(I2) := F;
  end TestB04;

  procedure TestB05
	    (A: in out Arr2T; I1, I2: in IT1; J1, J2: IT2; E, F: in ET1)
  is
  begin
    A(J1)(I1) := E;
    A(J2)(I2) := F;
  end TestB05;

  procedure TestB06
	    (A: in out Arr2T; I1, I2: in IT1; J1, J2: IT2; E, F: in ET1)
  is
  begin
    A(J1)(I1) := E;
    A(J2)(I2) := F;
  end TestB06;

  procedure TestB07
            (A: in out Arr2T; I: in IT2; B: in Arr1T)
  is
  begin
    A(I) := B;
  end TestB07;

  procedure TestB08
            (A: in out Arr2T; I: in IT2; B: in Arr1T)
  is
  begin
    A(I) := B;
  end TestB08;

  procedure TestB09
            (A: in out Arr2T; I: in IT2; B: in Arr1T)
  is
  begin
    A(I) := B;
  end TestB09;

  procedure TestB10
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
  is
    J_Next: IT2;
    F: ET1;
  begin
    A(J)(I) := E;
    if J=IT2'Last then
      J_Next := IT2'First;
    else
      J_Next := J + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J_Next)(I) := F;
  end TestB10;

  procedure TestB11
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
  is
    J_Next: IT2;
    F: ET1;
  begin
    A(J)(I) := E;
    if J=IT2'Last then
      J_Next := IT2'First;
    else
      J_Next := J + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J_Next)(I) := F;
  end TestB11;

  procedure TestB12
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
  is
    J_Next: IT2;
    F: ET1;
    T: Arr2T;
  begin
    T := A;
    A(J)(I) := E;
    pragma Assert_And_Cut (A = T'Update (J => T(J)'Update (I => E)));
    if J=IT2'Last then
      J_Next := IT2'First;
    else
      J_Next := J + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J_Next)(I) := F;
  end TestB12;

  procedure TestB13
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
  is
    J_Next: IT2;
    F: ET1;
    T: Arr2T;
  begin
    T := A;
    A(J)(I) := E;
    pragma Assert_And_Cut (A = T'Update (J => T(J)'Update (I => E)));
    if J=IT2'Last then
      J_Next := IT2'First;
    else
      J_Next := J + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J_Next)(I) := F;
  end TestB13;

  procedure TestB14
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
  is
    J_Next: IT2;
    F: ET1;
    T: Arr2T;
  begin
    T := A;
    A(J)(I) := E;
    if J=IT2'Last then
      J_Next := IT2'First;
    else
      J_Next := J + 1;
    end if;
    pragma Assert_And_Cut (A = T'Update (J => T(J)'Update (I => E)) and ((J=IT2'Last and J_Next=IT2'First) or (J<IT2'Last and J_Next=J+1)) and J_Next in IT2);
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J_Next)(I) := F;
  end TestB14;

  procedure TestB15
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
  is
    J_Next: IT2;
    F: ET1;
    T: Arr2T;
  begin
    T := A;
    A(J)(I) := E;
    if J=IT2'Last then
      J_Next := IT2'First;
    else
      J_Next := J + 1;
    end if;
    pragma Assert_And_Cut (A = T'Update (J => T(J)'Update (I => E)) and ((J=IT2'Last and J_Next=IT2'First) or (J<IT2'Last and J_Next=J+1)) and J_Next in IT2);
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(J_Next)(I) := F;
  end TestB15;

  procedure TestB16
            (A: in out Arr2T; I, J: in IT2; B, C: in Arr1T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestB16;

  procedure TestB17
            (A: in out Arr2T; I, J: in IT2; B, C: in Arr1T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestB17;

  procedure TestB18
            (A: in out Arr2T; I, J: in IT2; B, C: in Arr1T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestB18;

  procedure TestB19
	    (A: out Arr2T; B: in Arr2T)
  is
  begin
    A := B;
  end TestB19;

  procedure TestB20
	    (A: in out Arr2T; B: in Arr1T; I: in IT2)
  is
  begin
    A(I) := B;
  end TestB20;

  procedure TestB21
	    (A: in out Arr2T; B, C: in Arr1T; I, J: in IT2)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestB21;

  procedure TestB22
	    (A: out Arr2T; B: in Arr2T; I: in IT2; J: in IT1; E: in ET1)
  is
  begin
    A := B;
    A(I)(J) := E;
  end TestB22;

  -----------------------------------------------
  -- [C] Array of array of array tests
  -----------------------------------------------
  procedure TestC01
	    (A: in out Arr3T; I1: in IT1; I2: in IT2; I3: in IT3; E: in ET1)
  is
  begin
    A(I3)(I2)(I1) := E;
  end TestC01;

  procedure TestC02
	    (A: in out Arr3T; I1: in IT1; I2: in IT2; I3: in IT3; E: in ET1)
  is
  begin
    A(I3)(I2)(I1) := E;
  end TestC02;

  procedure TestC03
	    (A: in out Arr3T; I1: in IT1; I2: in IT2; I3: in IT3; E: in ET1)
  is
  begin
    A(I3)(I2)(I1) := E;
  end TestC03;

  procedure TestC04
	    (A: in out Arr3T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; E, F: in ET1)
  is
  begin
    A(K1)(J1)(I1) := E;
    A(K2)(J2)(I2) := F;
  end TestC04;

  procedure TestC05
	    (A: in out Arr3T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; E, F: in ET1)
  is
  begin
    A(K1)(J1)(I1) := E;
    A(K2)(J2)(I2) := F;
  end TestC05;

  procedure TestC06
	    (A: in out Arr3T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; E, F: in ET1)
  is
  begin
    A(K1)(J1)(I1) := E;
    A(K2)(J2)(I2) := F;
  end TestC06;

  procedure TestC07
            (A: in out Arr3T; I: in IT3; B: in Arr2T)
  is
  begin
    A(I) := B;
  end TestC07;

  procedure TestC08
            (A: in out Arr3T; I: in IT3; B: in Arr2T)
  is
  begin
    A(I) := B;
  end TestC08;

  procedure TestC09
            (A: in out Arr3T; I: in IT3; B: in Arr2T)
  is
  begin
    A(I) := B;
  end TestC09;

  procedure TestC10
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr1T)
  is
  begin
    A(I)(J) := B;
  end TestC10;

  procedure TestC11
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr1T)
  is
  begin
    A(I)(J) := B;
  end TestC11;

  procedure TestC12
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr1T)
  is
  begin
    A(I)(J) := B;
  end TestC12;

  procedure TestC13
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr2T; C: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
  end TestC13;

  procedure TestC14
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr2T; C: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
  end TestC14;

  procedure TestC15
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr2T; C: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
  end TestC15;

  procedure TestC16
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
  is
    K_Next: IT3;
    F: ET1;
  begin
    A(K)(J)(I) := E;
    if K=IT3'Last then
      K_Next := IT3'First;
    else
      K_Next := K + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(K_Next)(J)(I) := F;
  end TestC16;

  procedure TestC17
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
  is
    K_Next: IT3;
    F: ET1;
  begin
    A(K)(J)(I) := E;
    if K=IT3'Last then
      K_Next := IT3'First;
    else
      K_Next := K + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(K_Next)(J)(I) := F;
  end TestC17;

  procedure TestC18
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
  is
    K_Next: IT3;
    F: ET1;
    T: Arr3T;
  begin
    T := A;
    A(K)(J)(I) := E;
    pragma Assert_And_Cut (A = T'Update (K => T(K)'Update (J => T(K)(J)'Update (I => E))));
    if K=IT3'Last then
      K_Next := IT3'First;
    else
      K_Next := K + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(K_Next)(J)(I) := F;
  end TestC18;

  procedure TestC19
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
  is
    K_Next: IT3;
    F: ET1;
    T: Arr3T;
  begin
    T := A;
    A(K)(J)(I) := E;
    pragma Assert_And_Cut (A = T'Update (K => T(K)'Update (J => T(K)(J)'Update (I => E))));
    if K=IT3'Last then
      K_Next := IT3'First;
    else
      K_Next := K + 1;
    end if;
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(K_Next)(J)(I) := F;
  end TestC19;

  procedure TestC20
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
  is
    K_Next: IT3;
    F: ET1;
    T: Arr3T;
  begin
    T := A;
    A(K)(J)(I) := E;
    if K=IT3'Last then
      K_Next := IT3'First;
    else
      K_Next := K + 1;
    end if;
    pragma Assert_And_Cut (A = T'Update (K => T(K)'Update (J => T(K)(J)'Update (I => E))) and ((K=IT3'Last and K_Next=IT3'First) or (K<IT3'Last and K_Next=K+1)) and K_Next in IT3);
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(K_Next)(J)(I) := F;
  end TestC20;

  procedure TestC21
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
  is
    K_Next: IT3;
    F: ET1;
    T: Arr3T;
  begin
    T := A;
    A(K)(J)(I) := E;
    if K=IT3'Last then
      K_Next := IT3'First;
    else
      K_Next := K + 1;
    end if;
    pragma Assert_And_Cut (A = T'Update (K => T(K)'Update (J => T(K)(J)'Update (I => E))) and ((K=IT3'Last and K_Next=IT3'First) or (K<IT3'Last and K_Next=K+1)) and K_Next in IT3);
    if E = ET1'First then
      F := ET1'Last;
    else
      F := E - 1;
    end if;
    A(K_Next)(J)(I) := F;
  end TestC21;

  procedure TestC22
            (A: in out Arr3T; I, J: in IT3; B, C: in Arr2T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestC22;

  procedure TestC23
            (A: in out Arr3T; I, J: in IT3; B, C: in Arr2T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestC23;

  procedure TestC24
            (A: in out Arr3T; I, J: in IT3; B, C: in Arr2T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestC24;

  procedure TestC25
            (A: in out Arr3T; I, J: in IT3; B, C: in Arr2T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestC25;

  procedure TestC26
            (A: in out Arr3T; I: in IT3; J: in IT2; B: Arr2T; C: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
  end TestC26;

  procedure TestC27
            (A: in out Arr3T; I: in IT3; J: in IT2; B: Arr2T; C: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
  end TestC27;

  procedure TestC28
            (A: in out Arr3T; I: in IT3; J: in IT2; B: Arr2T; C: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
  end TestC28;

  procedure TestC29
            (A: in out Arr3T; I: in IT3; J: in IT2; B: Arr2T; C: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
  end TestC29;

  procedure TestC30
            (A: in out Arr3T; I1, I2: in IT3; J1, J2: in IT2; B, C: in Arr1T)
  is
  begin
    A(I1)(J1) := B;
    A(I2)(J2) := C;
  end TestC30;

  procedure TestC31
            (A: in out Arr3T; I1, I2: in IT3; J1, J2: in IT2; B, C: in Arr1T)
  is
  begin
    A(I1)(J1) := B;
    A(I2)(J2) := C;
  end TestC31;

  procedure TestC32
            (A: in out Arr3T; I1, I2: in IT3; J1, J2: in IT2; B, C: in Arr1T)
  is
  begin
    A(I1)(J1) := B;
    A(I2)(J2) := C;
  end TestC32;

  procedure TestC33
            (A: in out Arr3T; I1, I2: in IT3; J1, J2: in IT2; B, C: in Arr1T)
  is
  begin
    A(I1)(J1) := B;
    A(I2)(J2) := C;
  end TestC33;

  procedure TestC34
	    (A: out Arr3T; B: in Arr3T)
  is
  begin
    A := B;
  end TestC34;

  procedure TestC35
	    (A: out Arr3T; B: in Arr3T; I: in IT3; J: in IT2; K: in IT1; C: in Arr2T;
             D: in Arr1T; E: in ET1)
  is
  begin
    A := B;
    A(I) := C;
    A(I)(J) := D;
    A(I)(J)(K) := E;
  end TestC35;

  -----------------------------------------------
  -- [D] Array of array of array of array tests
  -----------------------------------------------
  procedure TestD01
	    (A: in out Arr4T; I1: in IT1; I2: in IT2; I3: in IT3; I4: in IT4; E: in ET1)
  is
  begin
    A(I4)(I3)(I2)(I1) := E;
  end TestD01;

  procedure TestD02
	    (A: in out Arr4T; I1: in IT1; I2: in IT2; I3: in IT3; I4: in IT4; E: in ET1)
  is
  begin
    A(I4)(I3)(I2)(I1) := E;
  end TestD02;

  procedure TestD03
	    (A: in out Arr4T; I1: in IT1; I2: in IT2; I3: in IT3; I4: in IT4; E: in ET1)
  is
  begin
    A(I4)(I3)(I2)(I1) := E;
  end TestD03;

  procedure TestD04
	    (A: in out Arr4T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; L1, L2: in IT4;
             E, F: in ET1)
  is
  begin
    A(L1)(K1)(J1)(I1) := E;
    A(L2)(K2)(J2)(I2) := F;
  end TestD04;

  procedure TestD05
	    (A: in out Arr4T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; L1, L2: in IT4;
             E, F: in ET1)
  is
  begin
    A(L1)(K1)(J1)(I1) := E;
    A(L2)(K2)(J2)(I2) := F;
  end TestD05;

  procedure TestD06
	    (A: in out Arr4T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; L1, L2: in IT4;
             E, F: in ET1)
  is
  begin
    A(L1)(K1)(J1)(I1) := E;
    A(L2)(K2)(J2)(I2) := F;
  end TestD06;

  procedure TestD07
            (A: in out Arr4T; I: in IT4; B: in Arr3T)
  is
  begin
    A(I) := B;
  end TestD07;

  procedure TestD08
            (A: in out Arr4T; I: in IT4; B: in Arr3T)
  is
  begin
    A(I) := B;
  end TestD08;

  procedure TestD09
            (A: in out Arr4T; I: in IT4; B: in Arr3T)
  is
  begin
    A(I) := B;
  end TestD09;

  procedure TestD10
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: in Arr3T; C: in Arr2T;
             D: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
    A(I)(J)(K) := D;
  end TestD10;

  procedure TestD11
            (A: in out Arr4T; I, J: in IT4; B, C: in Arr3T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestD11;

  procedure TestD12
            (A: in out Arr4T; I, J: in IT4; B, C: in Arr3T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestD12;

  procedure TestD13
            (A: in out Arr4T; I, J: in IT4; B, C: in Arr3T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestD13;

  procedure TestD14
            (A: in out Arr4T; I, J: in IT4; B, C: in Arr3T)
  is
  begin
    A(I) := B;
    A(J) := C;
  end TestD14;

  procedure TestD15
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: Arr3T; C: in Arr2T;
	     D: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
    A(I)(J)(K) := D;
  end TestD15;

  procedure TestD16
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: Arr3T; C: in Arr2T;
	     D: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
    A(I)(J)(K) := D;
  end TestD16;

  procedure TestD17
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: Arr3T; C: in Arr2T;
	     D: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
    A(I)(J)(K) := D;
  end TestD17;

  procedure TestD18
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: Arr3T; C: in Arr2T;
	     D: in Arr1T)
  is
  begin
    A(I) := B;
    A(I)(J) := C;
    A(I)(J)(K) := D;
  end TestD18;

  procedure TestD19
            (A: in out Arr4T; I1, I2: in IT4; J1, J2: in IT3; K1, K2: in IT2; B, C: in Arr1T)
  is
  begin
    A(I1)(J1)(K1) := B;
    A(I2)(J2)(K2) := C;
  end TestD19;

  procedure TestD20
            (A: in out Arr4T; I1, I2: in IT4; J1, J2: in IT3; K1, K2: in IT2; B, C: in Arr1T)
  is
  begin
    A(I1)(J1)(K1) := B;
    A(I2)(J2)(K2) := C;
  end TestD20;

  procedure TestD21
            (A: in out Arr4T; I1, I2: in IT4; J1, J2: in IT3; K1, K2: in IT2; B, C: in Arr1T)
  is
  begin
    A(I1)(J1)(K1) := B;
    A(I2)(J2)(K2) := C;
  end TestD21;

  procedure TestD22
            (A: in out Arr4T; I1, I2: in IT4; J1, J2: in IT3; K1, K2: in IT2; B, C: in Arr1T)
  is
  begin
    A(I1)(J1)(K1) := B;
    A(I2)(J2)(K2) := C;
  end TestD22;

  -----------------------------------------------
  -- [E] Simple record tests
  -----------------------------------------------
  procedure TestE01
	    (R: in out Rec1T; E: in ET1)
  is
  begin
    R.F1 := E;
  end TestE01;

  procedure TestE02
	    (R: in out Rec1T; E: in ET1)
  is
  begin
    R.F1 := E;
  end TestE02;

  procedure TestE03
	    (R: in out Rec1T; E: in ET1)
  is
  begin
    R.F1 := E;
  end TestE03;

  procedure TestE04
	    (R: out Rec1T; E: in ET1; F: in ET2)
  is
  begin
    R.F1 := E;
    R.G1 := F;
  end TestE04;

  procedure TestE05
	    (R: out Rec1T; E: in ET1; F: in ET2)
  is
  begin
    R.F1 := E;
    R.G1 := F;
  end TestE05;

  procedure TestE06
	    (R: in out Rec1T)
  is
    Temp: ET2;
  begin
    Temp := R.F1;
    R.F1 := R.G1;
    R.G1 := Temp;
  end TestE06;

  procedure TestE07
	    (R: in out Rec1T)
  is
    Temp: ET2;
  begin
    Temp := R.F1;
    R.F1 := R.G1;
    R.G1 := Temp;
  end TestE07;

  procedure TestE08
	    (R: in out Rec1T)
  is
    Temp: ET2;
  begin
    Temp := R.F1;
    R.F1 := R.G1;
    R.G1 := Temp;
  end TestE08;

  procedure TestE09
	    (R: out Rec1T; S: in Rec1T)
  is
  begin
    R := S;
    R.F1 := 25;
  end TestE09;

  procedure TestE10
	    (R: out Rec1T; S: in Rec1T)
  is
  begin
    R := S;
    R.F1 := 25;
  end TestE10;

  procedure TestE11
	    (R: out Rec1T; S: in Rec1T)
  is
  begin
    R := S;
    R.F1 := 25;
  end TestE11;

  -----------------------------------------------
  -- [F] Record of record tests
  -----------------------------------------------
  procedure TestF01
	    (R: in out Rec2T; E: in ET2)
  is
  begin
    R.G2.G1 := E;
  end TestF01;

  procedure TestF02
	    (R: in out Rec2T; E: in ET2)
  is
  begin
    R.G2.G1 := E;
  end TestF02;

  procedure TestF03
	    (R: in out Rec2T; E: in ET2)
  is
  begin
    R.G2.G1 := E;
  end TestF03;

  procedure TestF04
	    (R: in out Rec2T; E: in ET2)
  is
  begin
    R.G2.G1 := E;
  end TestF04;

  procedure TestF05
	    (R: in out Rec2T; E: in ET1; F: in ET2)
  is
  begin
    R.G2.F1 := E;
    R.G2.G1 := F;
  end TestF05;

  procedure TestF06
	    (R: in out Rec2T; E: in ET1; F: in ET2)
  is
  begin
    R.G2.F1 := E;
    R.G2.G1 := F;
  end TestF06;

  procedure TestF07
	    (R: in out Rec2T; E: in ET1; F: in ET2)
  is
  begin
    R.G2.F1 := E;
    R.G2.G1 := F;
  end TestF07;

  procedure TestF08
	    (R: in out Rec2T; E: in ET1; F: in ET2)
  is
  begin
    R.G2.F1 := E;
    R.G2.G1 := F;
  end TestF08;

  procedure TestF09
	    (R: in out Rec2T; E: in ET1; F: in ET2)
  is
  begin
    R.G2.F1 := E;
    R.G2.G1 := F;
  end TestF09;

  procedure TestF10
	    (R: in out Rec2T)
  is
    Temp: ET2;
  begin
    Temp := R.G2.F1;
    R.G2.F1 := R.G2.G1;
    R.G2.G1 := Temp;
  end TestF10;

  procedure TestF11
	    (R: in out Rec2T)
  is
    Temp: ET2;
  begin
    Temp := R.G2.F1;
    R.G2.F1 := R.G2.G1;
    R.G2.G1 := Temp;
  end TestF11;

  procedure TestF12
	    (R: in out Rec2T)
  is
    Temp: ET2;
  begin
    Temp := R.G2.F1;
    R.G2.F1 := R.G2.G1;
    R.G2.G1 := Temp;
  end TestF12;

  procedure TestF13
	    (R: in out Rec2T)
  is
    Temp: ET2;
  begin
    Temp := R.G2.F1;
    R.G2.F1 := R.G2.G1;
    R.G2.G1 := Temp;
  end TestF13;

  procedure TestF14
	    (R: in out Rec2T; A: in Rec1T)
  is
  begin
    R.G2 := A;
  end TestF14;

  procedure TestF15
	    (R: in out Rec2T; A: in Rec1T)
  is
  begin
    R.G2 := A;
  end TestF15;

  procedure TestF16
	    (R: in out Rec2T; A: in Rec1T)
  is
  begin
    R.G2 := A;
  end TestF16;

  procedure TestF17
	    (R: in out Rec2T; A: in Rec1T)
  is
  begin
    R.G2 := A;
  end TestF17;

  procedure TestF18
	    (R: in out Rec2T; A: in Rec1T)
  is
  begin
    R.G2 := A;
  end TestF18;

  procedure TestF19
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
  is
  begin
    R.G2 := A;
    R.G2.F1 := E;
  end TestF19;

  procedure TestF20
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
  is
  begin
    R.G2 := A;
    R.G2.F1 := E;
  end TestF20;

  procedure TestF21
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
  is
  begin
    R.G2 := A;
    R.G2.F1 := E;
  end TestF21;

  procedure TestF22
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
  is
  begin
    R.G2 := A;
    R.G2.F1 := E;
  end TestF22;

  procedure TestF23
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
  is
  begin
    R.G2 := A;
    R.G2.F1 := E;
  end TestF23;

  -----------------------------------------------
  -- [G] Record of record of record tests
  -----------------------------------------------
  procedure TestG01
	    (R: in out Rec3T; E: in ET1)
  is
  begin
    R.F3.G2.F1 := E;
  end TestG01;

  procedure TestG02
	    (R: in out Rec3T; E: in ET1)
  is
  begin
    R.F3.G2.F1 := E;
  end TestG02;

  procedure TestG03
	    (R: in out Rec3T; E: in ET1)
  is
  begin
    R.F3.G2.F1 := E;
  end TestG03;

  procedure TestG04
	    (R: in out Rec3T; E: in ET1)
  is
  begin
    R.F3.G2.F1 := E;
  end TestG04;

  procedure TestG05
	    (R: in out Rec3T; E: in ET1; F: in ET3; G: in ET4)
  is
  begin
    R.F3.G2.F1 := E;
    R.F3.H2 := E1Tc;
    R.G3 := G;
    R.F3.F2 := F;
  end TestG05;

  procedure TestG06
	    (R: in out Rec3T; E: in ET1; F: in ET3; G: in ET4)
  is
  begin
    R.F3.G2.F1 := E;
    R.F3.H2 := E1Tc;
    R.G3 := G;
    R.F3.F2 := F;
  end TestG06;

  procedure TestG07
	    (R: in out Rec3T; E: in ET1; F: in ET3; G: in ET4)
  is
  begin
    R.F3.G2.F1 := E;
    R.F3.H2 := E1Tc;
    R.G3 := G;
    R.F3.F2 := F;
  end TestG07;

  procedure TestG08
	    (R: in out Rec3T; E: in ET1; F: in ET3; G: in ET4)
  is
  begin
    R.F3.G2.F1 := E;
    R.F3.H2 := E1Tc;
    R.G3 := G;
    R.F3.F2 := F;
  end TestG08;

  procedure TestG09
	    (R: in out Rec3T)
  is
    Temp: ET2;
  begin
    Temp := R.F3.G2.F1;
    R.F3.G2.F1 := R.F3.G2.G1;
    R.F3.G2.G1 := Temp;
  end TestG09;

  procedure TestG10
	    (R: in out Rec3T)
  is
    Temp: ET2;
  begin
    Temp := R.F3.G2.F1;
    R.F3.G2.F1 := R.F3.G2.G1;
    R.F3.G2.G1 := Temp;
  end TestG10;

  procedure TestG11
	    (R: in out Rec3T)
  is
    Temp: ET2;
  begin
    Temp := R.F3.G2.F1;
    R.F3.G2.F1 := R.F3.G2.G1;
    R.F3.G2.G1 := Temp;
  end TestG11;

  procedure TestG12
	    (R: in out Rec3T)
  is
    Temp: ET2;
  begin
    Temp := R.F3.G2.F1;
    R.F3.G2.F1 := R.F3.G2.G1;
    R.F3.G2.G1 := Temp;
  end TestG12;

  procedure TestG13
	    (R: in out Rec3T; A: in Rec1T)
  is
  begin
    R.F3.G2 := A;
  end TestG13;

  procedure TestG14
	    (R: in out Rec3T; A: in Rec1T)
  is
  begin
    R.F3.G2 := A;
  end TestG14;

  procedure TestG15
	    (R: in out Rec3T; A: in Rec1T)
  is
  begin
    R.F3.G2 := A;
  end TestG15;

  procedure TestG16
	    (R: in out Rec3T; A: in Rec1T)
  is
  begin
    R.F3.G2 := A;
  end TestG16;

  procedure TestG17
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
  is
  begin
    R.F3 := A;
    R.F3.G2.F1 := E;
  end TestG17;

  procedure TestG18
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
  is
  begin
    R.F3 := A;
    R.F3.G2.F1 := E;
  end TestG18;

  procedure TestG19
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
  is
  begin
    R.F3 := A;
    R.F3.G2.F1 := E;
  end TestG19;

  procedure TestG20
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
  is
  begin
    R.F3 := A;
    R.F3.G2.F1 := E;
  end TestG20;

  procedure TestG21
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
  is
  begin
    R.F3 := A;
    R.F3.G2.F1 := E;
  end TestG21;

  procedure TestG22
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
  is
  begin
    R.F3 := A;
    R.F3.G2 := B;
  end TestG22;

  procedure TestG23
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
  is
  begin
    R.F3 := A;
    R.F3.G2 := B;
  end TestG23;

  procedure TestG24
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
  is
  begin
    R.F3 := A;
    R.F3.G2 := B;
  end TestG24;

  procedure TestG25
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
  is
  begin
    R.F3 := A;
    R.F3.G2 := B;
  end TestG25;

  procedure TestG26
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
  is
  begin
    R.F3 := A;
    R.F3.G2 := B;
  end TestG26;

  -----------------------------------------------
  -- [H] Record of record of record of record tests
  -----------------------------------------------
  procedure TestH01
	    (R: in out Rec4T; E: in ET1)
  is
  begin
    R.F4.F3.G2.F1 := E;
  end TestH01;

  procedure TestH02
	    (R: in out Rec4T; E: in ET1)
  is
  begin
    R.F4.F3.G2.F1 := E;
  end TestH02;

  procedure TestH03
	    (R: in out Rec4T; E: in ET1)
  is
  begin
    R.F4.F3.G2.F1 := E;
  end TestH03;

  procedure TestH04
	    (R: in out Rec4T; E: in ET1)
  is
  begin
    R.F4.F3.G2.F1 := E;
  end TestH04;

  procedure TestH05
	    (R: in out Rec4T; E: in ET1; F: in ET2)
  is
  begin
    R.F4.F3.G2.F1 := E;
    R.F4.F3.G2.G1 := F;
  end TestH05;

  procedure TestH06
	    (R: in out Rec4T; E: in ET1; F: in ET2)
  is
  begin
    R.F4.F3.G2.F1 := E;
    R.F4.F3.G2.G1 := F;
  end TestH06;

  procedure TestH07
	    (R: in out Rec4T; E: in ET1; F: in ET2)
  is
  begin
    R.F4.F3.G2.F1 := E;
    R.F4.F3.G2.G1 := F;
  end TestH07;

  procedure TestH08
	    (R: in out Rec4T; E: in ET1; F: in ET2)
  is
  begin
    R.F4.F3.G2.F1 := E;
    R.F4.F3.G2.G1 := F;
  end TestH08;

  procedure TestH09
	    (R: in out Rec4T)
  is
    Temp: Enum1TA;
  begin
    Temp := R.G4;
    R.G4 := R.F4.F3.H2;
    R.F4.F3.H2 := Temp;
  end TestH09;

  procedure TestH10
	    (R: in out Rec4T)
  is
    Temp: Enum1TA;
  begin
    Temp := R.G4;
    R.G4 := R.F4.F3.H2;
    R.F4.F3.H2 := Temp;
  end TestH10;

  procedure TestH11
	    (R: in out Rec4T)
  is
    Temp: Enum1TA;
  begin
    Temp := R.G4;
    R.G4 := R.F4.F3.H2;
    R.F4.F3.H2 := Temp;
  end TestH11;

  procedure TestH12
	    (R: in out Rec4T)
  is
    Temp: Enum1TA;
  begin
    Temp := R.G4;
    R.G4 := R.F4.F3.H2;
    R.F4.F3.H2 := Temp;
  end TestH12;

  procedure TestH13
	    (R: in out Rec4T)
  is
    Temp: Enum1TA;
  begin
    Temp := R.F4.F3.H2;
    R.F4.F3.H2 := R.G4;
    R.G4 := Temp;
  end TestH13;

  procedure TestH14
	    (R: in out Rec4T)
  is
    Temp: Enum1TA;
  begin
    Temp := R.F4.F3.H2;
    R.F4.F3.H2 := R.G4;
    R.G4 := Temp;
  end TestH14;

  procedure TestH15
	    (R: in out Rec4T)
  is
    Temp: Enum1TA;
  begin
    Temp := R.F4.F3.H2;
    R.F4.F3.H2 := R.G4;
    R.G4 := Temp;
  end TestH15;

  procedure TestH16
	    (R: in out Rec4T)
  is
    Temp: Enum1TA;
  begin
    Temp := R.F4.F3.H2;
    R.F4.F3.H2 := R.G4;
    R.G4 := Temp;
  end TestH16;

  procedure TestH17
	    (R: in out Rec4T; A: in Rec3T; B: in Rec2T; C: in Rec1T; D: in ET1)
  is
  begin
    R.F4 := A;
    R.F4.F3 := B;
    R.F4.F3.G2 := C;
    R.F4.F3.G2.F1 := D;
  end TestH17;

  procedure TestH18
	    (R: in out Rec4T; A: in Rec3T; B: in Rec2T; C: in Rec1T; D: in ET1)
  is
  begin
    R.F4 := A;
    R.F4.F3 := B;
    R.F4.F3.G2 := C;
    R.F4.F3.G2.F1 := D;
  end TestH18;

  procedure TestH19
	    (R: in out Rec4T; A: in Rec3T; B: in Rec2T; C: in Rec1T; D: in ET1)
  is
  begin
    R.F4 := A;
    R.F4.F3 := B;
    R.F4.F3.G2 := C;
    R.F4.F3.G2.F1 := D;
  end TestH19;

  procedure TestH20
	    (R: in out Rec4T; A: in Rec3T; B: in Rec2T; C: in Rec1T; D: in ET1)
  is
  begin
    R.F4 := A;
    R.F4.F3 := B;
    R.F4.F3.G2 := C;
    R.F4.F3.G2.F1 := D;
  end TestH20;

  -----------------------------------------------
  -- [I] Mixed nested record tests
  -----------------------------------------------
  procedure TestI01
	    (R: in out Rec5T; A, B: in Rec1T)
  is
  begin
    R.F5.G2 := A;
    R.H5 := B;
  end TestI01;

  procedure TestI02
	    (R: in out Rec5T; A, B: in Rec1T)
  is
  begin
    R.F5.G2 := A;
    R.H5 := B;
  end TestI02;

  procedure TestI03
	    (R: in out Rec5T; A, B: in Rec1T)
  is
  begin
    R.F5.G2 := A;
    R.H5 := B;
  end TestI03;

  procedure TestI04
	    (R: in out Rec5T; A, B: in Rec1T)
  is
  begin
    R.F5.G2 := A;
    R.H5 := B;
  end TestI04;

  procedure TestI05
	    (R: in out Rec5T)
  is
    Temp: Rec1T;
  begin
    Temp := R.H5;
    R.H5 := R.F5.G2;
    R.F5.G2 := Temp;
  end TestI05;

  procedure TestI06
	    (R: in out Rec5T)
  is
    Temp: Rec1T;
  begin
    Temp := R.H5;
    R.H5 := R.F5.G2;
    R.F5.G2 := Temp;
  end TestI06;

  procedure TestI07
	    (R: in out Rec5T)
  is
    Temp: Rec1T;
  begin
    Temp := R.H5;
    R.H5 := R.F5.G2;
    R.F5.G2 := Temp;
  end TestI07;

  procedure TestI08
	    (R: in out Rec5T)
  is
    Temp: Rec1T;
  begin
    Temp := R.H5;
    R.H5 := R.F5.G2;
    R.F5.G2 := Temp;
  end TestI08;

  procedure TestI09
	    (R: in out Rec5T)
  is
    Temp: Rec1T;
  begin
    Temp := R.F5.G2;
    R.F5.G2 := R.H5;
    R.H5 := Temp;
  end TestI09;

  procedure TestI10
	    (R: in out Rec5T)
  is
    Temp: Rec1T;
  begin
    Temp := R.F5.G2;
    R.F5.G2 := R.H5;
    R.H5 := Temp;
  end TestI10;

  procedure TestI11
	    (R: in out Rec5T)
  is
    Temp: Rec1T;
  begin
    Temp := R.F5.G2;
    R.F5.G2 := R.H5;
    R.H5 := Temp;
  end TestI11;

  procedure TestI12
	    (R: in out Rec5T)
  is
    Temp: Rec1T;
  begin
    Temp := R.F5.G2;
    R.F5.G2 := R.H5;
    R.H5 := Temp;
  end TestI12;

  -----------------------------------------------
  -- [J] Array(1) of record(1)
  -----------------------------------------------
  procedure TestJ01
	    (A: in out AofR1; I: in IT1; F: in ET1)
  is
  begin
    A(I).F1 := F;
  end TestJ01;

  procedure TestJ02
	    (A: in out AofR1; I: in IT1; F: in ET1)
  is
  begin
    A(I).F1 := F;
  end TestJ02;

  procedure TestJ03
	    (A: in out AofR1; I: in IT1; F: in ET1)
  is
  begin
    A(I).F1 := F;
  end TestJ03;

  procedure TestJ04
	    (A: in out AofR1; I: in IT1; F: in ET1)
  is
  begin
    A(I).F1 := F;
  end TestJ04;

  procedure TestJ05
	    (A: in out AofR1; I, J: in IT1; F, G: in ET1)
  is
  begin
    A(I).F1 := F;
    A(J).F1 := G;
  end TestJ05;

  procedure TestJ06
	    (A: in out AofR1; I, J: in IT1; F, G: in ET1)
  is
  begin
    A(I).F1 := F;
    A(J).F1 := G;
  end TestJ06;

  procedure TestJ07
	    (A: in out AofR1; I, J: in IT1; F, G: in ET1)
  is
  begin
    A(I).F1 := F;
    A(J).F1 := G;
  end TestJ07;

  procedure TestJ08
	    (A: in out AofR1; I, J: in IT1; F, G: in ET1)
  is
  begin
    A(I).F1 := F;
    A(J).F1 := G;
  end TestJ08;

  procedure TestJ09
	    (A: in out AofR1; I, J: in IT1)
  is
    Temp: ET2;
  begin
    Temp := A(I).G1;
    A(I).G1 := A(J).G1;
    A(J).G1 := Temp;
  end TestJ09;

  procedure TestJ10
	    (A: in out AofR1; I, J: in IT1)
  is
    Temp: ET2;
  begin
    Temp := A(I).G1;
    A(I).G1 := A(J).G1;
    A(J).G1 := Temp;
  end TestJ10;

  procedure TestJ11
	    (A: in out AofR1; I, J: in IT1)
  is
    Temp: ET2;
  begin
    Temp := A(I).G1;
    A(I).G1 := A(J).G1;
    A(J).G1 := Temp;
  end TestJ11;

  procedure TestJ12
	    (A: in out AofR1; I, J: in IT1)
  is
    Temp: ET2;
  begin
    Temp := A(I).G1;
    A(I).G1 := A(J).G1;
    A(J).G1 := Temp;
  end TestJ12;

  procedure TestJ13
	    (A: in out AofR1; I: in IT1; R: in Rec1T)
  is
  begin
    A(I) := R;
  end TestJ13;

  procedure TestJ14
	    (A: in out AofR1; I: in IT1; R: in Rec1T)
  is
  begin
    A(I) := R;
  end TestJ14;

  procedure TestJ15
	    (A: in out AofR1; I: in IT1; R: in Rec1T)
  is
  begin
    A(I) := R;
  end TestJ15;

  procedure TestJ16
	    (A: in out AofR1; I: in IT1; R: in Rec1T)
  is
  begin
    A(I) := R;
  end TestJ16;

  procedure TestJ17
	    (A: in out AofR1; I: in IT1; R: in Rec1T; E: ET1)
  is
  begin
    A(I) := R;
    A(I).F1 := E;
  end TestJ17;

  procedure TestJ18
	    (A: in out AofR1; I: in IT1; R: in Rec1T; E: ET1)
  is
  begin
    A(I) := R;
    A(I).F1 := E;
  end TestJ18;

  procedure TestJ19
	    (A: in out AofR1; I: in IT1; R: in Rec1T; E: ET1)
  is
  begin
    A(I) := R;
    A(I).F1 := E;
  end TestJ19;

  procedure TestJ20
	    (A: in out AofR1; I: in IT1; R: in Rec1T; E: ET1)
  is
  begin
    A(I) := R;
    A(I).F1 := E;
  end TestJ20;

  -----------------------------------------------
  -- [K] Array(1) of record(2)
  -----------------------------------------------
  procedure TestK01
	    (A: in out AofR2; I: in IT2; F: in ET1)
  is
  begin
    A(I).G2.F1 := F;
  end TestK01;

  procedure TestK02
	    (A: in out AofR2; I: in IT2; F: in ET1)
  is
  begin
    A(I).G2.F1 := F;
  end TestK02;

  procedure TestK03
	    (A: in out AofR2; I: in IT2; F: in ET1)
  is
  begin
    A(I).G2.F1 := F;
  end TestK03;

  procedure TestK04
	    (A: in out AofR2; I: in IT2; F: in ET1)
  is
  begin
    A(I).G2.F1 := F;
  end TestK04;

  procedure TestK05
	    (A: in out AofR2; I: in IT2; E: in ET3; F: in ET1; G: in ET2; H: in Enum1TA)
  is
  begin
    A(I).F2 := E;
    A(I).G2.F1 := F;
    A(I).G2.G1 := G;
    A(I).H2 := H;
  end TestK05;

  procedure TestK06
	    (A: in out AofR2; I: in IT2; E: in ET3; F: in ET1; G: in ET2; H: in Enum1TA)
  is
  begin
    A(I).F2 := E;
    A(I).G2.F1 := F;
    A(I).G2.G1 := G;
    A(I).H2 := H;
  end TestK06;

  procedure TestK07
	    (A: in out AofR2; I: in IT2; E: in ET3; F: in ET1; G: in ET2; H: in Enum1TA)
  is
  begin
    A(I).F2 := E;
    A(I).G2.F1 := F;
    A(I).G2.G1 := G;
    A(I).H2 := H;
  end TestK07;

  procedure TestK08
	    (A: in out AofR2; I: in IT2; E: in ET3; F: in ET1; G: in ET2; H: in Enum1TA)
  is
  begin
    A(I).F2 := E;
    A(I).G2.F1 := F;
    A(I).G2.G1 := G;
    A(I).H2 := H;
  end TestK08;

  -----------------------------------------------
  -- [L] Array(1) of record(3)
  -----------------------------------------------
  procedure TestL01
	    (A: in out AofR3; I: in IT3; F: in ET1)
  is
  begin
    A(I).F3.G2.F1 := F;
  end TestL01;

  procedure TestL02
	    (A: in out AofR3; I: in IT3; F: in ET1)
  is
  begin
    A(I).F3.G2.F1 := F;
  end TestL02;

  procedure TestL03
	    (A: in out AofR3; I: in IT3; F: in ET1)
  is
  begin
    A(I).F3.G2.F1 := F;
  end TestL03;

  procedure TestL04
	    (A: in out AofR3; I: in IT3; F: in ET1)
  is
  begin
    A(I).F3.G2.F1 := F;
  end TestL04;

  procedure TestL05
	    (A: in out AofR3; I: in IT3; D: in ET4; E: in ET3; F: in ET1; G: in ET2;
	     H: in Enum1TA)
  is
  begin
    A(I).G3 := D;
    A(I).F3.F2 := E;
    A(I).F3.G2.F1 := F;
    A(I).F3.G2.G1 := G;
    A(I).F3.H2 := H;
  end TestL05;

  procedure TestL06
	    (A: in out AofR3; I: in IT3; D: in ET4; E: in ET3; F: in ET1; G: in ET2;
	     H: in Enum1TA)
  is
  begin
    A(I).G3 := D;
    A(I).F3.F2 := E;
    A(I).F3.G2.F1 := F;
    A(I).F3.G2.G1 := G;
    A(I).F3.H2 := H;
  end TestL06;

  procedure TestL07
	    (A: in out AofR3; I: in IT3; D: in ET4; E: in ET3; F: in ET1; G: in ET2;
	     H: in Enum1TA)
  is
  begin
    A(I).G3 := D;
    A(I).F3.F2 := E;
    A(I).F3.G2.F1 := F;
    A(I).F3.G2.G1 := G;
    A(I).F3.H2 := H;
  end TestL07;

  procedure TestL08
	    (A: in out AofR3; I: in IT3; D: in ET4; E: in ET3; F: in ET1; G: in ET2;
	     H: in Enum1TA)
  is
  begin
    A(I).G3 := D;
    A(I).F3.F2 := E;
    A(I).F3.G2.F1 := F;
    A(I).F3.G2.G1 := G;
    A(I).F3.H2 := H;
  end TestL08;

  -----------------------------------------------
  -- [M] Array(1) of record(mixed)
  -----------------------------------------------
  procedure TestM01
	    (A: in out AofR4; I: in IT4; F, G: in ET1)
  is
  begin
    A(I).F5.G2.F1 := F;
    A(I).H5.F1 := G;
  end TestM01;

  procedure TestM02
	    (A: in out AofR4; I: in IT4; F, G: in ET1)
  is
  begin
    A(I).F5.G2.F1 := F;
    A(I).H5.F1 := G;
  end TestM02;

  procedure TestM03
	    (A: in out AofR4; I: in IT4; F, G: in ET1)
  is
  begin
    A(I).F5.G2.F1 := F;
    A(I).H5.F1 := G;
  end TestM03;

  procedure TestM04
	    (A: in out AofR4; I: in IT4; F, G: in ET1)
  is
  begin
    A(I).F5.G2.F1 := F;
    A(I).H5.F1 := G;
  end TestM04;

  -----------------------------------------------
  -- [N] Record(1) of array(1)
  -----------------------------------------------
  procedure TestN01
	    (R: in out RofA1; I: in IT1; E: in ET1)
  is
  begin
    R.S1(I) := E;
  end TestN01;

  procedure TestN02
	    (R: in out RofA1; I: in IT1; E: in ET1)
  is
  begin
    R.S1(I) := E;
  end TestN02;

  procedure TestN03
	    (R: in out RofA1; I: in IT1; E: in ET1)
  is
  begin
    R.S1(I) := E;
  end TestN03;

  procedure TestN04
	    (R: in out RofA1; I: in IT1; E: in ET1)
  is
  begin
    R.S1(I) := E;
  end TestN04;

  procedure TestN05
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
  is
  begin
    R.S1(I) := E;
    R.T1 := F;
  end TestN05;

  procedure TestN06
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
  is
  begin
    R.S1(I) := E;
    R.T1 := F;
  end TestN06;

  procedure TestN07
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
  is
  begin
    R.S1(I) := E;
    R.T1 := F;
  end TestN07;

  procedure TestN08
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
  is
  begin
    R.S1(I) := E;
    R.T1 := F;
  end TestN08;

  procedure TestN09
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
  is
  begin
    R.T1 := F;
    R.S1(I) := E;
  end TestN09;

  procedure TestN10
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
  is
  begin
    R.T1 := F;
    R.S1(I) := E;
  end TestN10;

  procedure TestN11
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
  is
  begin
    R.T1 := F;
    R.S1(I) := E;
  end TestN11;

  procedure TestN12
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
  is
  begin
    R.T1 := F;
    R.S1(I) := E;
  end TestN12;

  procedure TestN13
	    (R: in out RofA1; I, J: in IT1; E, F: in ET1)
  is
  begin
    R.S1(I) := E;
    R.S1(J) := F;
  end TestN13;

  procedure TestN14
	    (R: in out RofA1; I, J: in IT1; E, F: in ET1)
  is
  begin
    R.S1(I) := E;
    R.S1(J) := F;
  end TestN14;

  procedure TestN15
	    (R: in out RofA1; I, J: in IT1; E, F: in ET1)
  is
  begin
    R.S1(I) := E;
    R.S1(J) := F;
  end TestN15;

  procedure TestN16
	    (R: in out RofA1; I, J: in IT1; E, F: in ET1)
  is
  begin
    R.S1(I) := E;
    R.S1(J) := F;
  end TestN16;

  procedure TestN17
	    (R: out RofA1; A: in Arr1T; E: in Enum2T)
  is
  begin
    R.S1 := A;
    R.T1 := E;
  end TestN17;

  procedure TestN18
	    (R: out RofA1; A: in Arr1T; E: in Enum2T)
  is
  begin
    R.S1 := A;
    R.T1 := E;
  end TestN18;

  procedure TestN19
	    (R: out RofA1; A: in Arr1T; E: in Enum2T)
  is
  begin
    R.S1 := A;
    R.T1 := E;
  end TestN19;

  -----------------------------------------------
  -- [O] Record(1) of array(2)
  -----------------------------------------------
  procedure TestO01
	    (R: in out RofA2; I: in IT2; J: in IT1; E: in ET1)
  is
  begin
    R.S2(I)(J) := E;
  end TestO01;

  procedure TestO02
	    (R: in out RofA2; I: in IT2; J: in IT1; E: in ET1)
  is
  begin
    R.S2(I)(J) := E;
  end TestO02;

  procedure TestO03
	    (R: in out RofA2; I: in IT2; J: in IT1; E: in ET1)
  is
  begin
    R.S2(I)(J) := E;
  end TestO03;

  procedure TestO04
	    (R: in out RofA2; I: in IT2; J: in IT1; E: in ET1)
  is
  begin
    R.S2(I)(J) := E;
  end TestO04;

  procedure TestO05
	    (R: in out RofA2; I1, I2: in IT2; J1, J2: in IT1; E, F: in ET1)
  is
  begin
    R.S2(I1)(J1) := E;
    R.S2(I2)(J2) := F;
  end TestO05;

  procedure TestO06
	    (R: in out RofA2; I1, I2: in IT2; J1, J2: in IT1; E, F: in ET1)
  is
  begin
    R.S2(I1)(J1) := E;
    R.S2(I2)(J2) := F;
  end TestO06;

  procedure TestO07
	    (R: in out RofA2; I1, I2: in IT2; J1, J2: in IT1; E, F: in ET1)
  is
  begin
    R.S2(I1)(J1) := E;
    R.S2(I2)(J2) := F;
  end TestO07;

  procedure TestO08
	    (R: in out RofA2; I: in IT2; A: in Arr1T)
  is
  begin
    R.S2(I) := A;
    R.S2(55-I)(1) := 0;  -- 55-I in 5..50, but 55-I /= I, since I is an integer
  end TestO08;

  procedure TestO09
	    (R: in out RofA2; I: in IT2; A: in Arr1T)
  is
  begin
    R.S2(I) := A;
    R.S2(55-I)(1) := 0;  -- 55-I in 5..50, but 55-I /= I, since I is an integer
  end TestO09;

  procedure TestO10
	    (R: in out RofA2; I: in IT2; A: in Arr1T)
  is
  begin
    R.S2(I) := A;
    R.S2(55-I)(1) := 0;  -- 55-I in 5..50, but 55-I /= I, since I is an integer
  end TestO10;

  -----------------------------------------------
  -- [P] Record(1) of array(3)
  -----------------------------------------------
  procedure TestP01
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; E: in ET1)
  is
  begin
    R.T3(I)(J)(K) := E;
  end TestP01;

  procedure TestP02
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; E: in ET1)
  is
  begin
    R.T3(I)(J)(K) := E;
  end TestP02;

  procedure TestP03
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; E: in ET1)
  is
  begin
    R.T3(I)(J)(K) := E;
  end TestP03;

  procedure TestP04
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; E: in ET1)
  is
  begin
    R.T3(I)(J)(K) := E;
  end TestP04;

  procedure TestP05
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; A: in Arr3T;
	     B: in Arr2T; C: in Arr1T; D: in ET1)
  is
  begin
    R.T3 := A;
    R.T3(I) := B;
    R.T3(I)(J) := C;
    R.T3(I)(J)(K) := D;
    R.U3 := false;
  end TestP05;

  procedure TestP06
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; A: in Arr3T;
	     B: in Arr2T; C: in Arr1T; D: in ET1)
  is
  begin
    R.T3 := A;
    R.T3(I) := B;
    R.T3(I)(J) := C;
    R.T3(I)(J)(K) := D;
    R.U3 := false;
  end TestP06;

  procedure TestP07
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; A: in Arr3T;
	     B: in Arr2T; C: in Arr1T; D: in ET1)
  is
  begin
    R.T3 := A;
    R.T3(I) := B;
    R.T3(I)(J) := C;
    R.T3(I)(J)(K) := D;
    R.U3 := false;
  end TestP07;

  procedure TestP08
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; A: in Arr3T;
	     B: in Arr2T; C: in Arr1T; D: in ET1)
  is
  begin
    R.T3 := A;
    R.T3(I) := B;
    R.T3(I)(J) := C;
    R.T3(I)(J)(K) := D;
    R.U3 := false;
  end TestP08;

  -----------------------------------------------
  -- [Q] Record(1) of array(mixed)
  -----------------------------------------------
  procedure TestQ01
	    (R: in out RofA4; I: in IT2; J: in IT1; E, F: in ET1)
  is
  begin
    R.S4(J) := E;
    R.T4(I)(J) := F;
  end TestQ01;

  procedure TestQ02
	    (R: in out RofA4; I: in IT2; J: in IT1; E, F: in ET1)
  is
  begin
    R.S4(J) := E;
    R.T4(I)(J) := F;
  end TestQ02;

  procedure TestQ03
	    (R: in out RofA4; I: in IT2; J: in IT1; E, F: in ET1)
  is
  begin
    R.S4(J) := E;
    R.T4(I)(J) := F;
  end TestQ03;

  procedure TestQ04
	    (R: in out RofA4; I: in IT2; J: in IT1; E, F: in ET1)
  is
  begin
    R.S4(J) := E;
    R.T4(I)(J) := F;
  end TestQ04;

  -----------------------------------------------
  -- [R] Array of record of array(1)
  -----------------------------------------------
  procedure TestR01
	    (A: in out AofRofA1; I: in IT3; J: in IT1; E: in ET1)
  is
  begin
    A(I).S1(J) := E;
  end TestR01;

  procedure TestR02
	    (A: in out AofRofA1; I: in IT3; J: in IT1; E: in ET1)
  is
  begin
    A(I).S1(J) := E;
  end TestR02;

  procedure TestR03
	    (A: in out AofRofA1; I: in IT3; J: in IT1; E: in ET1)
  is
  begin
    A(I).S1(J) := E;
  end TestR03;

  procedure TestR04
	    (A: in out AofRofA1; I: in IT3; J: in IT1; E: in ET1)
  is
  begin
    A(I).S1(J) := E;
  end TestR04;

  procedure TestR05
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
  is
  begin
    A(I).S1(J) := E;
    A(X) := R;
  end TestR05;

  procedure TestR06
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
  is
  begin
    A(I).S1(J) := E;
    A(X) := R;
  end TestR06;

  procedure TestR07
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
  is
  begin
    A(I).S1(J) := E;
    A(X) := R;
  end TestR07;

  procedure TestR08
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
  is
  begin
    A(I).S1(J) := E;
    A(X) := R;
  end TestR08;

  procedure TestR09
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
  is
  begin
    A(I).S1(J) := E;
    A(X) := R;
  end TestR09;

  procedure TestR10
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
  is
  begin
    A(I).S1(J) := E;
    A(X) := R;
  end TestR10;

  procedure TestR11
	    (A: out AofRofA1; I: in IT3; J: in IT1; B: in AofRofA1; C: RofA1; D: Arr1T;
	     E: in ET1)
  is
  begin
    A := B;
    A(I) := C;
    A(I).S1 := D;
    A(I).S1(J) := E;
  end TestR11;

  procedure TestR12
	    (A: out AofRofA1; I: in IT3; J: in IT1; B: in AofRofA1; C: RofA1; D: Arr1T;
	     E: in ET1)
  is
  begin
    A := B;
    A(I) := C;
    A(I).S1 := D;
    A(I).S1(J) := E;
  end TestR12;

  procedure TestR13
	    (A: out AofRofA1; I: in IT3; J: in IT1; B: in AofRofA1; C: RofA1; D: Arr1T;
	     E: in ET1)
  is
  begin
    A := B;
    A(I) := C;
    A(I).S1 := D;
    A(I).S1(J) := E;
  end TestR13;

  procedure TestR14
	    (A: out AofRofA1; I: in IT3; J: in IT1; B: in AofRofA1; C: RofA1; D: Arr1T;
	     E: in ET1)
  is
  begin
    A := B;
    A(I) := C;
    A(I).S1 := D;
    A(I).S1(J) := E;
  end TestR14;

  -----------------------------------------------
  -- [S] Array of record of array(mixed)
  -----------------------------------------------
  procedure TestS01
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E: in ET1)
  is
  begin
    A(I).T4(J)(K) := E;
  end TestS01;

  procedure TestS02
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E: in ET1)
  is
  begin
    A(I).T4(J)(K) := E;
  end TestS02;

  procedure TestS03
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E: in ET1)
  is
  begin
    A(I).T4(J)(K) := E;
  end TestS03;

  procedure TestS04
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E: in ET1)
  is
  begin
    A(I).T4(J)(K) := E;
  end TestS04;

  procedure TestS05
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E, F: in ET1)
  is
  begin
    A(I).T4(J)(K) := E;
    A(I).S4(K) := F;
  end TestS05;

  procedure TestS06
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E, F: in ET1)
  is
  begin
    A(I).T4(J)(K) := E;
    A(I).S4(K) := F;
  end TestS06;

  procedure TestS07
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E, F: in ET1)
  is
  begin
    A(I).T4(J)(K) := E;
    A(I).S4(K) := F;
  end TestS07;

  procedure TestS08
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E, F: in ET1)
  is
  begin
    A(I).T4(J)(K) := E;
    A(I).S4(K) := F;
  end TestS08;

  -----------------------------------------------
  -- [T] Record of array of record(1)
  -----------------------------------------------
  procedure TestT01
	    (R: in out RofAofR1; I: in IT1; E: in ET1)
  is
  begin
    R.A1(I).F1 := E;
  end TestT01;

  procedure TestT02
	    (R: in out RofAofR1; I: in IT1; E: in ET1)
  is
  begin
    R.A1(I).F1 := E;
  end TestT02;

  procedure TestT03
	    (R: in out RofAofR1; I: in IT1; E: in ET1)
  is
  begin
    R.A1(I).F1 := E;
  end TestT03;

  procedure TestT04
	    (R: in out RofAofR1; I: in IT1; E: in ET1)
  is
  begin
    R.A1(I).F1 := E;
  end TestT04;

  procedure TestT05
	    (R: in out RofAofR1; I: in IT1; E: in ET1; F: in ET2)
  is
  begin
    R.A1(I).F1 := E;
    R.B1 := true;
    R.A1(I).G1 := F;
  end TestT05;

  procedure TestT06
	    (R: in out RofAofR1; I: in IT1; E: in ET1; F: in ET2)
  is
  begin
    R.A1(I).F1 := E;
    R.B1 := true;
    R.A1(I).G1 := F;
  end TestT06;

  procedure TestT07
	    (R: in out RofAofR1; I: in IT1; E: in ET1; F: in ET2)
  is
  begin
    R.A1(I).F1 := E;
    R.B1 := true;
    R.A1(I).G1 := F;
  end TestT07;

  procedure TestT08
	    (R: in out RofAofR1; I: in IT1; E: in ET1; F: in ET2)
  is
  begin
    R.A1(I).F1 := E;
    R.B1 := true;
    R.A1(I).G1 := F;
  end TestT08;

  -----------------------------------------------
  -- [U] Record of array of record(mixed)
  -----------------------------------------------
  procedure TestU01
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
  is
  begin
    R.B2(I).F5.G2.F1 := E;
  end TestU01;

  procedure TestU02
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
  is
  begin
    R.B2(I).F5.G2.F1 := E;
  end TestU02;

  procedure TestU03
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
  is
  begin
    R.B2(I).F5.G2.F1 := E;
  end TestU03;

  procedure TestU04
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
  is
  begin
    R.B2(I).F5.G2.F1 := E;
  end TestU04;

  procedure TestU05
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
  is
  begin
    R.B2(R.A2).F5.G2.F1 := E;
    R.A2 := I;
    R.B2(I).F5.G2.F1 := E;
  end TestU05;

  procedure TestU06
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
  is
  begin
    R.B2(R.A2).F5.G2.F1 := E;
    R.A2 := I;
    R.B2(I).F5.G2.F1 := E;
  end TestU06;

  procedure TestU07
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
  is
  begin
    R.B2(R.A2).F5.G2.F1 := E;
    R.A2 := I;
    R.B2(I).F5.G2.F1 := E;
  end TestU07;

  procedure TestU08
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
  is
  begin
    R.B2(R.A2).F5.G2.F1 := E;
    R.A2 := I;
    R.B2(I).F5.G2.F1 := E;
  end TestU08;

  -----------------------------------------------
  -- [V] Array of record of array of record
  -----------------------------------------------
  procedure TestV01
	    (A: in out AofRofAofR; I: in IT2; J: in IT1; E: in ET1)
  is
  begin
    A(I).A1(J).F1 := E;
  end TestV01;

  procedure TestV02
	    (A: in out AofRofAofR; I: in IT2; J: in IT1; E: in ET1)
  is
  begin
    A(I).A1(J).F1 := E;
  end TestV02;

  procedure TestV03
	    (A: in out AofRofAofR; I: in IT2; J: in IT1; E: in ET1)
  is
  begin
    A(I).A1(J).F1 := E;
  end TestV03;

  procedure TestV04
	    (A: in out AofRofAofR; I: in IT2; J: in IT1; E: in ET1)
  is
  begin
    A(I).A1(J).F1 := E;
  end TestV04;

  -----------------------------------------------
  -- [W] Record of array of record of array
  -----------------------------------------------
  procedure TestW01
	    (R: in out RofAofRofA; I: in IT3; J: in IT1; E: in ET1)
  is
  begin
    R.D1(I).S1(J) := E;
  end TestW01;

  procedure TestW02
	    (R: in out RofAofRofA; I: in IT3; J: in IT1; E: in ET1)
  is
  begin
    R.D1(I).S1(J) := E;
  end TestW02;

  procedure TestW03
	    (R: in out RofAofRofA; I: in IT3; J: in IT1; E: in ET1)
  is
  begin
    R.D1(I).S1(J) := E;
  end TestW03;

  procedure TestW04
	    (R: in out RofAofRofA; I: in IT3; J: in IT1; E: in ET1)
  is
  begin
    R.D1(I).S1(J) := E;
  end TestW04;

end AR;
