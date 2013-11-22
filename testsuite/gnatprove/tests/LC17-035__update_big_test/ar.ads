package AR is

  -----------------------------------------------
  -- INTEGER TYPES AND SUBTYPES
  -----------------------------------------------
  type NatByte is range 0..255;

  subtype IT1 is NatByte range  1..10;
  subtype IT2 is NatByte range  5..50;
  subtype IT3 is NatByte range  1..16;
  subtype IT4 is NatByte range 90..99;

  subtype ET1 is NatByte range  0..99;
  subtype ET2 is NatByte range  1..25;
  subtype ET3 is NatByte range 10..90;
  subtype ET4 is NatByte range 50..59;

  -----------------------------------------------
  -- ENUMERATION TYPES AND SUBTYPES
  -----------------------------------------------
  type Enum1T is (E1Ta, E1Tb, E1Tc, E1Td, E1Te, E1Tf, E1Tg);
  type Enum2T is (E2Ta, E2Tb, E2Tc, E2Td, E2Te, E2Tf);

  subtype Enum1TA is Enum1T range E1Tb..E1Te;
  subtype Enum1TB is Enum1T range E1Tc..E1Tg;

  subtype Enum2TA is Enum2T range E2Tc..E2Td;

  -----------------------------------------------
  -- RECORD TYPES (INCLUDING RECORDS OF RECORDS)
  -----------------------------------------------
  type Rec1T is record		-- simple flat record
    F1: ET1;
    G1: ET2;
  end record;

  type Rec2T is record		-- nested record (1 deep)
    F2: ET3;
    G2: Rec1T;
    H2: Enum1TA;
  end record;

  type Rec3T is record		-- nested record (2 deep)
    F3: Rec2T;
    G3: ET4;
  end record;

  type Rec4T is record		-- nested record (3 deep)
    F4: Rec3T;
    G4: Enum1T;
  end record;

  type Rec5T is record		-- nested record (2 deep + 1 deep)
    F5: Rec2T;
    G5: Boolean;
    H5: Rec1T;
  end record;

  -----------------------------------------------
  -- ARRAY TYPES (INCLUDING ARRAYS OF ARRAYS)
  -----------------------------------------------
  type Arr1T is array (IT1) of ET1;

  type Arr2T is array (IT2) of Arr1T;

  type Arr3T is array (IT3) of Arr2T;

  type Arr4T is array (IT4) of Arr3T;

  -----------------------------------------------
  -- MIXED: (ARRAYS OF [RECORDS) OF ARRAYS]...
  -----------------------------------------------
  -- (1) ARRAYS OF RECORDS
  type AofR1 is array (IT1) of Rec1T;		-- array of record
  type AofR2 is array (IT2) of Rec2T;		-- array of record of record
  type AofR3 is array (IT3) of Rec3T;		-- array of record of record of record
  type AofR4 is array (IT4) of Rec5T;		-- array of nested (2+1 deep) records

  -- (2) RECORDS OF ARRAYS
  type RofA1 is record				-- record of array
    S1: Arr1T;
    T1: Enum2T;
  end record;

  type RofA2 is record				-- record of array of array
    S2: Arr2T;
    T2: Boolean;
  end record;

  type RofA3 is record				-- record of array of array of array
    S3: Enum1TB;
    T3: Arr3T;
    U3: Boolean;
  end record;

  type RofA4 is record				-- record of two (2+1 dim) arrays
    S4: Arr1T;
    T4: Arr2T;
  end record;

  -- (3) ARRAYS OF RECORDS OF ARRAYS
  type AofRofA1 is array (IT3) of RofA1;
  type AofRofA2 is array (IT4) of RofA4;

  -- (4) RECORDS OF ARRAYS OF RECORDS
  type RofAofR1 is record			-- record containing an array of records
    A1: AofR1;
    B1: Boolean;
    C1: Enum1T;
  end record;

  type RofAofR2 is record			-- record containing an array of nested (2+1 deep) records
    A2: IT4;
    B2: AofR4;
  end record;

  -- (5) ARRAYS OF RECORDS OF ARRAYS OF RECORDS
  type AofRofAofR is array (IT2) of RofAofR1;

  -- (6) RECORDS OF ARRAYS OF RECORDS OF ARRAYS
  type RofAofRofA is record
    D1: AofRofA1;
    E1: Arr1T;
  end record;


  -----------------------------------------------
  -- PROCEDURES
  -----------------------------------------------

  -----------------------------------------------
  -- [A] Simple one-dimensional arrays
  -----------------------------------------------
  procedure TestA01
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => (for all N in IT1 => (A(N) in ET1));

  procedure TestA02
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => (for all N in IT1 => (if N /= I then A (N) = A'Old (N))) and A (I) = E;

  procedure TestA03
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => A = A'Old'Update (I => E);

  procedure TestA04
	    (A: in out Arr1T; I, J: in IT1; E, F: in ET1)
     with Depends => (A =>+ (E, F, I, J)),
          Post    => (for all N in IT1 => (A(N) in ET1));

  procedure TestA05
	    (A: in out Arr1T; I, J: in IT1; E, F: in ET1)
     with Depends => (A =>+ (E, F, I, J)),
          Pre     => I /= J,
          Post    => (for all N in IT1 => (if (N /= I and N /= J) then A (N) = A'Old (N))) and A (I) = E and A (J) = F;

  procedure TestA06
	    (A: in out Arr1T; I, J: in IT1; E, F: in ET1)
     with Depends => (A =>+ (E, F, I, J)),
          Pre     => I /= J,
          Post    => A = A'Old'Update (I => E, J => F);

  procedure TestA07
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => (for all N in IT1 => (A(N) in ET1));

  procedure TestA08
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => ( (I < IT1'Last and ( (E > ET1'First and A = A'Old'Update (I => E, I+1 => E-1)) or (E = ET1'First and A = A'Old'Update (I => E, I+1 => ET1'Last)) )) or (I = IT1'Last and ( (E > ET1'First and A = A'Old'Update (I => E, IT1'First => E-1)) or (E = ET1'First and A = A'Old'Update (I => E, IT1'First => ET1'Last)) )) );

  procedure TestA09
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => (for all N in IT1 => (A(N) in ET1));

  procedure TestA10
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => ( (I < IT1'Last and ( (E > ET1'First and A = A'Old'Update (I => E, I+1 => E-1)) or (E = ET1'First and A = A'Old'Update (I => E, I+1 => ET1'Last)) )) or (I = IT1'Last and ( (E > ET1'First and A = A'Old'Update (I => E, IT1'First => E-1)) or (E = ET1'First and A = A'Old'Update (I => E, IT1'First => ET1'Last)) )) );

  procedure TestA11
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => (for all N in IT1 => (A(N) in ET1));

  procedure TestA12
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => ( (I < IT1'Last and ( (E > ET1'First and A = A'Old'Update (I => E, I+1 => E-1)) or (E = ET1'First and A = A'Old'Update (I => E, I+1 => ET1'Last)) )) or (I = IT1'Last and ( (E > ET1'First and A = A'Old'Update (I => E, IT1'First => E-1)) or (E = ET1'First and A = A'Old'Update (I => E, IT1'First => ET1'Last)) )) );

  procedure TestA13
	    (A: in out Arr1T; I: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I)),
          Post    => A(1) in ET1 and A(2) in ET1 and A(3) in ET1 and A(4) in ET1 and A(5)  in ET1 and A(6) in ET1 and A(7) in ET1 and A(8) in ET1 and A(9) in ET1 and A(10) in ET1;

  procedure TestA14
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => (for all N in IT1 => (A(N) in ET1));

  procedure TestA15
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => A(1) in ET1 and A(2) in ET1 and A(3) in ET1 and A(4) in ET1 and A(5)  in ET1 and A(6) in ET1 and A(7) in ET1 and A(8) in ET1 and A(9) in ET1 and A(10) in ET1;

  procedure TestA16
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => (for all N in IT1 => (A(N) in ET1));

  procedure TestA17
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => (for all N in IT1 => (if N /= 5 then A (N) = B (N))) and A (5) = 25;

  procedure TestA18
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => A(1) in ET1 and A(2) in ET1 and A(3) in ET1 and A(4) in ET1 and A(5)  in ET1 and A(6) in ET1 and A(7) in ET1 and A(8) in ET1 and A(9) in ET1 and A(10) in ET1;

  procedure TestA19
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => (for all N in IT1 => (A(N) in ET1));

  procedure TestA20
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => (for all N in IT1 => (A(N) = 0));

  procedure TestA21
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => A(1) in ET1 and A(2) in ET1 and A(3) in ET1 and A(4) in ET1 and A(5)  in ET1 and A(6) in ET1 and A(7) in ET1 and A(8) in ET1 and A(9) in ET1 and A(10) in ET1;

  procedure TestA22
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => A(1) = 0 and A(2) = 0 and A(3) = 0 and A(4) = 0 and A(5)  = 0 and A(6) = 0 and A(7) = 0 and A(8) = 0 and A(9) = 0 and A(10) = 0;

  procedure TestA23
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => (for all N in IT1 => (A(N) in ET1));

  procedure TestA24
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => (for all N in IT1 => (A(N) = B(11-N)));

  procedure TestA25
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => A(1) in ET1 and A(2) in ET1 and A(3) in ET1 and A(4) in ET1 and A(5)  in ET1 and A(6) in ET1 and A(7) in ET1 and A(8) in ET1 and A(9) in ET1 and A(10) in ET1;

  procedure TestA26
	    (A: out Arr1T; B: in Arr1T)
     with Depends => (A => B),
          Post    => A(1) = B(10) and A(2) = B(9) and A(3) = B(8) and A(4) = B(7) and A(5) = B(6) and A(6) = B(5) and A(7) = B(4) and A(8) = B(3) and A(9) = B(2) and A(10) = B(1);

  -----------------------------------------------
  -- [B] Array of array tests
  -----------------------------------------------
  procedure TestB01
	    (A: in out Arr2T; I1: in IT1; I2: in IT2; E: in ET1)
     with Depends => (A =>+ (E, I1, I2)),
          Post    => (for all M in IT2 => (for all N in IT1 => (for all M in IT2 => (A(M)(N) in ET1))));

  procedure TestB02
	    (A: in out Arr2T; I1: in IT1; I2: in IT2; E: in ET1)
     with Depends => (A =>+ (E, I1, I2)),
          Post    => (for all N in IT1 => (for all M in IT2 => (if (M /= I2 or N /= I1) then A (M) (N) = A'Old (M) (N)))) and A (I2) (I1) = E;

  procedure TestB03
	    (A: in out Arr2T; I1: in IT1; I2: in IT2; E: in ET1)
     with Depends => (A =>+ (E, I1, I2)),
          Post    => A = A'Old'Update (I2 => A'Old(I2)'Update (I1 => E));

  procedure TestB04
	    (A: in out Arr2T; I1, I2: in IT1; J1, J2: IT2; E, F: in ET1)
     with Depends => (A =>+ (E, F, I1, I2, J1, J2)),
          Post    => (for all N in IT1 => (for all M in IT2 => (A(M)(N) in ET1)));

  procedure TestB05
	    (A: in out Arr2T; I1, I2: in IT1; J1, J2: IT2; E, F: in ET1)
     with Depends => (A =>+ (E, F, I1, I2, J1, J2)),
          Pre     => I1 /= I2 and J1 /= J2,
          Post    => (for all N in IT1 => (for all M in IT2 => (if ((M /= J1 or N /= I1) and (M /= J2 or N /= I2)) then A (M) (N) = A'Old (M) (N)))) and A (J1) (I1) = E and A (J2) (I2) = F;

  procedure TestB06
	    (A: in out Arr2T; I1, I2: in IT1; J1, J2: IT2; E, F: in ET1)
     with Depends => (A =>+ (E, F, I1, I2, J1, J2)),
          Pre     => I1 /= I2 or J1 /= J2,
          Post    => (if J1 /= J2 then A = A'Old'Update (J1 => A'Old (J1) 'Update (I1 => E), J2 => A'Old (J2) 'Update (I2 => F))) and (if J1 = J2 then A = A'Old'Update (J1 => A'Old (J1) 'Update (I1 => E, I2 => F)));

  procedure TestB07
            (A: in out Arr2T; I: in IT2; B: in Arr1T)
     with Depends => (A =>+ (B, I)),
          Post    => True;

  procedure TestB08
            (A: in out Arr2T; I: in IT2; B: in Arr1T)
     with Depends => (A =>+ (B, I)),
          Post    => (for all N in IT2 => (if N /= I then A (N) = A'Old (N))) and A (I) = B;

  procedure TestB09
            (A: in out Arr2T; I: in IT2; B: in Arr1T)
     with Depends => (A =>+ (B, I)),
          Post    => A = A'Old'Update (I => B);

  procedure TestB10
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => (for all N in IT1 => (for all M in IT2 => (A(M)(N) in ET1)));

  procedure TestB11
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => ( (J < IT2'Last and ( (E > ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), J+1 => A'Old(J+1)'Update (I => E-1))) or (E = ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), J+1 => A'Old(J+1)'Update (I => ET1'Last))) )) or (J = IT2'Last and ( (E > ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), IT2'First => A'Old(IT2'First)'Update (I => E-1))) or (E = ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), IT2'First => A'Old(IT2'First)'Update (I => ET1'Last))) )) );

  procedure TestB12
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => (for all N in IT1 => (for all M in IT2 => (A(M)(N) in ET1)));

  procedure TestB13
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => ( (J < IT2'Last and ( (E > ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), J+1 => A'Old(J+1)'Update (I => E-1))) or (E = ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), J+1 => A'Old(J+1)'Update (I => ET1'Last))) )) or (J = IT2'Last and ( (E > ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), IT2'First => A'Old(IT2'First)'Update (I => E-1))) or (E = ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), IT2'First => A'Old(IT2'First)'Update (I => ET1'Last))) )) );

  procedure TestB14
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => (for all N in IT1 => (for all M in IT2 => (A(M)(N) in ET1)));

  procedure TestB15
	    (A: in out Arr2T; I: in IT1; J: in IT2; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => ( (J < IT2'Last and ( (E > ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), J+1 => A'Old(J+1)'Update (I => E-1))) or (E = ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), J+1 => A'Old(J+1)'Update (I => ET1'Last))) )) or (J = IT2'Last and ( (E > ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), IT2'First => A'Old(IT2'First)'Update (I => E-1))) or (E = ET1'First and A = A'Old'Update (J => A'Old(J)'Update (I => E), IT2'First => A'Old(IT2'First)'Update (I => ET1'Last))) )) );

  procedure TestB16
            (A: in out Arr2T; I, J: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => True;

  procedure TestB17
            (A: in out Arr2T; I, J: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
          Pre     => I /= J,
          Post    => (for all N in IT2 => (if (N /= I and N /= J) then A (N) = A'Old (N))) and A (I) = B and A (J) = C;

  procedure TestB18
            (A: in out Arr2T; I, J: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
          Pre     => I /= J,
          Post    => A = A'Old'Update (I => B, J => C);

  procedure TestB19
	    (A: out Arr2T; B: in Arr2T)
     with Depends => (A => B),
          Post    => (for all N in IT2 => (for all M in IT1 => (A(N)(M) in ET1)));

  procedure TestB20
	    (A: in out Arr2T; B: in Arr1T; I: in IT2)
     with Depends => (A =>+ (B, I)),
          Post    => (for all N in IT2 => (for all M in IT1 => (A(N)(M) in ET1)));

  procedure TestB21
	    (A: in out Arr2T; B, C: in Arr1T; I, J: in IT2)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => (for all N in IT2 => (for all M in IT1 => (A(N)(M) in ET1)));

  procedure TestB22
	    (A: out Arr2T; B: in Arr2T; I: in IT2; J: in IT1; E: in ET1)
     with Depends => (A => (B, E, I, J)),
          Post    => (for all N in IT2 => (for all M in IT1 => (A(N)(M) in ET1)));

  -----------------------------------------------
  -- [C] Array of array of array tests
  -----------------------------------------------
  procedure TestC01
	    (A: in out Arr3T; I1: in IT1; I2: in IT2; I3: in IT3; E: in ET1)
     with Depends => (A =>+ (E, I1, I2, I3)),
          Post    => (for all M in IT3 => (for all N in IT2 => (for all O in IT1 => (A(M)(N)(O) in ET1))));

  procedure TestC02
	    (A: in out Arr3T; I1: in IT1; I2: in IT2; I3: in IT3; E: in ET1)
     with Depends => (A =>+ (E, I1, I2, I3)),
          Post    => (for all O in IT1 => (for all N in IT2 => (for all M in IT3 => (if (M /= I3 or N /= I2 or O /= I1) then A (M) (N) (O) = A'Old (M) (N) (O))))) and A (I3) (I2) (I1) = E;

  procedure TestC03
	    (A: in out Arr3T; I1: in IT1; I2: in IT2; I3: in IT3; E: in ET1)
     with Depends => (A =>+ (E, I1, I2, I3)),
          Post    => A = A'Old'Update (I3 => A'Old(I3)'Update (I2 => A'Old(I3)(I2)'Update (I1 => E)));

  procedure TestC04
	    (A: in out Arr3T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; E, F: in ET1)
     with Depends => (A =>+ (E, F, I1, I2, J1, J2, K1, K2)),
          Post    => (for all O in IT1 => (for all N in IT2 => (for all M in IT3 => (A(M)(N)(O) in ET1))));

  procedure TestC05
	    (A: in out Arr3T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; E, F: in ET1)
     with Depends => (A =>+ (E, F, I1, I2, J1, J2, K1, K2)),
          Pre     => I1 /= I2 or J1 /= J2 or K1 /= K2,
          Post    => (for all O in IT1 => (for all N in IT2 => (for all M in IT3 => (if ((M /= K1 or N /= J1 or O /= I1) and (M /= K2 or N /= J2 or O /= I2)) then A (M) (N) (O) = A'Old (M) (N) (O))))) and A (K1) (J1) (I1) = E and A (K2) (J2) (I2) = F;

  procedure TestC06
	    (A: in out Arr3T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; E, F: in ET1)
     with Depends => (A =>+ (E, F, I1, I2, J1, J2, K1, K2)),
          Pre     => I1 /= I2 and J1 /= J2 and K1 /= K2,
          Post    => A = A'Old'Update (K1 => A'Old(K1)'Update (J1 => A'Old(K1)(J1)'Update (I1 => E)), K2 => A'Old(K2)'Update (J2 => A'Old(K2)(J2)'Update (I2 => F)));

  procedure TestC07
            (A: in out Arr3T; I: in IT3; B: in Arr2T)
     with Depends => (A =>+ (B, I)),
          Post    => (for all M in IT3 => (for all N in IT2 => (for all O in IT1 => (A(M)(N)(O) in ET1))));

  procedure TestC08
            (A: in out Arr3T; I: in IT3; B: in Arr2T)
     with Depends => (A =>+ (B, I)),
          Post    => (for all N in IT3 => (if N /= I then A (N) = A'Old (N))) and A (I) = B;

  procedure TestC09
            (A: in out Arr3T; I: in IT3; B: in Arr2T)
     with Depends => (A =>+ (B, I)),
          Post    => A = A'Old'Update (I => B);

  procedure TestC10
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr1T)
     with Depends => (A =>+ (B, I, J)),
          Post    => (for all M in IT3 => (for all N in IT2 => (for all O in IT1 => (A(M)(N)(O) in ET1))));

  procedure TestC11
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr1T)
     with Depends => (A =>+ (B, I, J)),
          Post    => (for all M in IT3 => (for all N in IT2 => (if (M /= I or N /= J) then A (M) (N) = A'Old (M) (N)))) and A (I) (J) = B;

  procedure TestC12
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr1T)
     with Depends => (A =>+ (B, I, J)),
          Post    => A = A'Old'Update (I => A'Old(I)'Update (J => B));

  procedure TestC13
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr2T; C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
    Post    => (for all M in IT3 => (for all N in IT2 => (for all O in IT1 => (A(M)(N)(O) in ET1))));

  procedure TestC14
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr2T; C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => (for all M in IT3 => (if M /= I then A (M) = A'Old (M))) and (for all N in IT2 => (if N /= J then A (I) (N) = B (N))) and A (I) (J) = C;

  procedure TestC15
            (A: in out Arr3T; I: in IT3; J: in IT2; B: in Arr2T; C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => A = A'Old'Update (I => B'Update (J => C));

  procedure TestC16
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => (for all O in IT1 => (for all N in IT2 => (for all M in IT3 => (A(M)(N)(O) in ET1))));

  procedure TestC17
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => ( (K < IT3'Last and ( (E > ET1'First and A = A'Old'Update (K   => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), K+1 => A'Old(K+1)'Update (J => A'Old(K+1)(J)'Update (I => E-1)))) or (E = ET1'First and A = A'Old'Update (K   => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), K+1 => A'Old(K+1)'Update (J => A'Old(K+1)(J)'Update (I => ET1'Last)))) )) or (K = IT3'Last and ( (E > ET1'First and A = A'Old'Update (K => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), IT3'First => A'Old(IT3'First)'Update (J => A'Old(IT3'First)(J)'Update (I => E-1)))) or (E = ET1'First and A = A'Old'Update (K => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), IT3'First => A'Old(IT3'First)'Update (J => A'Old(IT3'First)(J)'Update (I => ET1'Last)))) )) );

  procedure TestC18
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => (for all O in IT1 => (for all N in IT2 => (for all M in IT3 => (A(M)(N)(O) in ET1))));

  procedure TestC19
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => ( (K < IT3'Last and ( (E > ET1'First and A = A'Old'Update (K   => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), K+1 => A'Old(K+1)'Update (J => A'Old(K+1)(J)'Update (I => E-1)))) or (E = ET1'First and A = A'Old'Update (K   => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), K+1 => A'Old(K+1)'Update (J => A'Old(K+1)(J)'Update (I => ET1'Last)))) )) or (K = IT3'Last and ( (E > ET1'First and A = A'Old'Update (K => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), IT3'First => A'Old(IT3'First)'Update (J => A'Old(IT3'First)(J)'Update (I => E-1)))) or (E = ET1'First and A = A'Old'Update (K => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), IT3'First => A'Old(IT3'First)'Update (J => A'Old(IT3'First)(J)'Update (I => ET1'Last)))) )) );

  procedure TestC20
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => (for all O in IT1 => (for all N in IT2 => (for all M in IT3 => (A(M)(N)(O) in ET1))));

  procedure TestC21
	    (A: in out Arr3T; I: in IT1; J: in IT2; K: in IT3; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => ( (K < IT3'Last and ( (E > ET1'First and A = A'Old'Update (K   => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), K+1 => A'Old(K+1)'Update (J => A'Old(K+1)(J)'Update (I => E-1)))) or (E = ET1'First and A = A'Old'Update (K   => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), K+1 => A'Old(K+1)'Update (J => A'Old(K+1)(J)'Update (I => ET1'Last)))) )) or (K = IT3'Last and ( (E > ET1'First and A = A'Old'Update (K => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), IT3'First => A'Old(IT3'First)'Update (J => A'Old(IT3'First)(J)'Update (I => E-1)))) or (E = ET1'First and A = A'Old'Update (K => A'Old(K)'Update (J => A'Old(K)(J)'Update (I => E)), IT3'First => A'Old(IT3'First)'Update (J => A'Old(IT3'First)(J)'Update (I => ET1'Last)))) )) );

  procedure TestC22
            (A: in out Arr3T; I, J: in IT3; B, C: in Arr2T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => True;

  procedure TestC23
            (A: in out Arr3T; I, J: in IT3; B, C: in Arr2T)
     with Depends => (A =>+ (B, C, I, J)),
          Pre     => I /= J,
          Post    => (for all N in IT3 => (if (N /= I and N /= J) then A (N) = A'Old (N))) and A (I) = B and A (J) = C;

  procedure TestC24
            (A: in out Arr3T; I, J: in IT3; B, C: in Arr2T)
     with Depends => (A =>+ (B, C, I, J)),
          Pre     => I /= J,
          Post    => A = A'Old'Update (I => B, J => C);

  procedure TestC25
            (A: in out Arr3T; I, J: in IT3; B, C: in Arr2T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => (for all O in IT3 => (for all N in IT2 => (for all M in IT1 => (A(O)(N)(M) in ET1))));

  procedure TestC26
            (A: in out Arr3T; I: in IT3; J: in IT2; B: Arr2T; C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => True;

  procedure TestC27
            (A: in out Arr3T; I: in IT3; J: in IT2; B: Arr2T; C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => (for all N in IT3 => (if N /= I then A (N) = A'Old (N))) and (for all N in IT2 => (if N /= J then A (I) (N) = B (N))) and A (I) (J) = C;

  procedure TestC28
            (A: in out Arr3T; I: in IT3; J: in IT2; B: Arr2T; C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => A = A'Old'Update (I => B'Update (J => C));

  procedure TestC29
            (A: in out Arr3T; I: in IT3; J: in IT2; B: Arr2T; C: in Arr1T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => (for all O in IT3 => (for all N in IT2 => (for all M in IT1 => (A(O)(N)(M) in ET1))));

  procedure TestC30
            (A: in out Arr3T; I1, I2: in IT3; J1, J2: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I1, I2, J1, J2)),
          Post    => True;

  procedure TestC31
            (A: in out Arr3T; I1, I2: in IT3; J1, J2: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I1, I2, J1, J2)),
          Pre     => I1 /= I2 or J1 /= J2,
          Post    => (for all N in IT3 => (if (N /= I1 and N /= I2) then A (N) = A'Old (N))) and (if I1 = I2 then (for all N in IT2 => (if (N /= J1 and N /= J2) then A (I1) (N) = A'Old (I1) (N)))) and (if I1 /= I2 then ((for all N in IT2 => (if N /= J1 then A (I1) (N) = A'Old (I1) (N))) and (for all N in IT2 => (if N /= J2 then A (I2) (N) = A'Old (I2) (N))))) and A (I1) (J1) = B and A (I2) (J2) = C;

  procedure TestC32
            (A: in out Arr3T; I1, I2: in IT3; J1, J2: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I1, I2, J1, J2)),
          Pre     => I1 /= I2 or J1 /= J2,
          Post    => (if I1 /= I2 then A = A'Old'Update (I1 => A'Old (I1) 'Update (J1 => B), I2 => A'Old (I2) 'Update (J2 => C))) and (if I1 = I2 then A = A'Old'Update (I1 => A'Old (I1) 'Update (J1 => B, J2 => C)));

  procedure TestC33
            (A: in out Arr3T; I1, I2: in IT3; J1, J2: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I1, I2, J1, J2)),
          Post    => (for all O in IT3 => (for all N in IT2 => (for all M in IT1 => (A(O)(N)(M) in ET1))));

  procedure TestC34
	    (A: out Arr3T; B: in Arr3T)
     with Depends => (A => B),
          Post    => (for all O in IT3 => (for all N in IT2 => (for all M in IT1 => (A(O)(N)(M) in ET1))));

  procedure TestC35
	    (A: out Arr3T; B: in Arr3T; I: in IT3; J: in IT2; K: in IT1; C: in Arr2T;
             D: in Arr1T; E: in ET1)
     with Depends => (A => (B, C, D, E, I, J, K)),
          Post    => (for all O in IT3 => (for all N in IT2 => (for all M in IT1 => (A(O)(N)(M) in ET1))));

  -----------------------------------------------
  -- [D] Array of array of array of array tests
  -----------------------------------------------
  procedure TestD01
	    (A: in out Arr4T; I1: in IT1; I2: in IT2; I3: in IT3; I4: in IT4; E: in ET1)
     with Depends => (A =>+ (E, I1, I2, I3, I4)),
          Post    => (for all M in IT4 => (for all N in IT3 => (for all O in IT2 => (for all P in IT1 => (A(M)(N)(O)(P) in ET1)))));

  procedure TestD02
	    (A: in out Arr4T; I1: in IT1; I2: in IT2; I3: in IT3; I4: in IT4; E: in ET1)
     with Depends => (A =>+ (E, I1, I2, I3, I4)),
          Post    => (for all P in IT1 => (for all O in IT2 => (for all N in IT3 => (for all M in IT4 => (if (M /= I4 or N /= I3 or O /= I2 or P /= I1) then A (M) (N) (O) (P) = A'Old (M) (N) (O) (P)))))) and A (I4) (I3) (I2) (I1) = E;

  procedure TestD03
	    (A: in out Arr4T; I1: in IT1; I2: in IT2; I3: in IT3; I4: in IT4; E: in ET1)
     with Depends => (A =>+ (E, I1, I2, I3, I4)),
          Post    => A = A'Old'Update (I4 => A'Old(I4)'Update (I3 => A'Old(I4)(I3)'Update (I2 => A'Old(I4)(I3)(I2)'Update (I1 => E))));

  procedure TestD04
	    (A: in out Arr4T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; L1, L2: in IT4;
             E, F: in ET1)
     with Depends => (A =>+ (E, F, I1, I2, J1, J2, K1, K2, L1, L2)),
          Post    => (for all P in IT1 => (for all O in IT2 => (for all N in IT3 => (for all M in IT4 => (A(M)(N)(O)(P) in ET1)))));

  procedure TestD05
	    (A: in out Arr4T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; L1, L2: in IT4;
             E, F: in ET1)
     with Depends => (A =>+ (E, F, I1, I2, J1, J2, K1, K2, L1, L2)),
          Pre     => I1 /= I2 or J1 /= J2 or K1 /= K2 or L1 /= L2,
          Post    => (for all P in IT1 => (for all O in IT2 => (for all N in IT3 => (for all M in IT4 => (if ((M /= L1 or N /= K1 or O /= J1 or P /= I1) and (M /= L2 or N /= K2 or O /= J2 or P /= I2)) then A (M) (N) (O) (P) = A'Old (M) (N) (O) (P)))))) and A (L1) (K1) (J1) (I1) = E and A (L2) (K2) (J2) (I2) = F;

  procedure TestD06
	    (A: in out Arr4T; I1, I2: in IT1; J1, J2: in IT2; K1, K2: in IT3; L1, L2: in IT4;
             E, F: in ET1)
     with Depends => (A =>+ (E, F, I1, I2, J1, J2, K1, K2, L1, L2)),
          Pre     => I1 /= I2 and J1 /= J2 and K1 /= K2 and L1 /= L2,
          Post    => A = A'Old'Update (L1 => A'Old(L1)'Update (K1 => A'Old(L1)(K1)'Update (J1 => A'Old(L1)(K1)(J1)'Update (I1 => E))), L2 => A'Old(L2)'Update (K2 => A'Old(L2)(K2)'Update (J2 => A'Old(L2)(K2)(J2)'Update (I2 => F))));

  procedure TestD07
            (A: in out Arr4T; I: in IT4; B: in Arr3T)
     with Depends => (A =>+ (B, I)),
          Post    => (for all M in IT4 => (for all N in IT3 => (for all O in IT2 => (for all P in IT1 => (A(M)(N)(O)(P) in ET1)))));

  procedure TestD08
            (A: in out Arr4T; I: in IT4; B: in Arr3T)
     with Depends => (A =>+ (B, I)),
          Post    => (for all N in IT4 => (if N /= I then A (N) = A'Old (N))) and A (I) = B;

  procedure TestD09
            (A: in out Arr4T; I: in IT4; B: in Arr3T)
     with Depends => (A =>+ (B, I)),
          Post    => A = A'Old'Update (I => B);

  procedure TestD10
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: in Arr3T; C: in Arr2T;
	    D: in Arr1T)
     with Depends => (A =>+ (B, C, D, I, J, K)),
          Post    => A = A'Old'Update (I => B'Update (J => C'Update (K => D)));

  procedure TestD11
            (A: in out Arr4T; I, J: in IT4; B, C: in Arr3T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => True;

  procedure TestD12
            (A: in out Arr4T; I, J: in IT4; B, C: in Arr3T)
     with Depends => (A =>+ (B, C, I, J)),
          Pre     => I /= J,
          Post    => (for all N in IT4 => (if (N /= I and N /= J) then A (N) = A'Old (N))) and A (I) = B and A (J) = C;

  procedure TestD13
            (A: in out Arr4T; I, J: in IT4; B, C: in Arr3T)
     with Depends => (A =>+ (B, C, I, J)),
          Pre     => I /= J,
          Post    => A = A'Old'Update (I => B, J => C);

  procedure TestD14
            (A: in out Arr4T; I, J: in IT4; B, C: in Arr3T)
     with Depends => (A =>+ (B, C, I, J)),
          Post    => (for all P in IT4 => (for all O in IT3 => (for all N in IT2 => (for all M in IT1 => (A(P)(O)(N)(M) in ET1)))));

  procedure TestD15
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: Arr3T; C: in Arr2T;
	     D: in Arr1T)
     with Depends => (A =>+ (B, C, D, I, J, K)),
          Post    => True;

  procedure TestD16
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: Arr3T; C: in Arr2T;
	     D: in Arr1T)
     with Depends => (A =>+ (B, C, D, I, J, K)),
          Post    => (for all N in IT4 => (if N /= I then A (N) = A'Old (N))) and (for all N in IT3 => (if N /= J then A (I) (N) = B (N))) and (for all N in IT2 => (if N /= K then A (I) (J) (N) = C (N))) and A (I) (J) (K) = D;

  procedure TestD17
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: Arr3T; C: in Arr2T;
	     D: in Arr1T)
     with Depends => (A =>+ (B, C, D, I, J, K)),
          Post    => A = A'Old'Update (I => B'Update (J => C'Update (K => D)));

  procedure TestD18
            (A: in out Arr4T; I: in IT4; J: in IT3; K: in IT2; B: Arr3T; C: in Arr2T;
	     D: in Arr1T)
     with Depends => (A =>+ (B, C, D, I, J, K)),
          Post    => (for all P in IT4 => (for all O in IT3 => (for all N in IT2 => (for all M in IT1 => (A(P)(O)(N)(M) in ET1)))));

  procedure TestD19
            (A: in out Arr4T; I1, I2: in IT4; J1, J2: in IT3; K1, K2: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I1, I2, J1, J2, K1, K2)),
          Post    => True;

  procedure TestD20
            (A: in out Arr4T; I1, I2: in IT4; J1, J2: in IT3; K1, K2: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I1, I2, J1, J2, K1, K2)),
          Pre     => I1 /= I2 or J1 /= J2 or K1 /= K2,
          Post    => (for all M in IT4 => (for all N in IT3 => (for all O in IT2 => (if not ((M = I1 and N = J1 and O = K1) or (M = I2 and N = J2 and O = K2)) then A (M) (N) (O) = A'Old (M) (N) (O))))) and A (I1) (J1) (K1) = B and A (I2) (J2) (K2) = C;

  procedure TestD21
            (A: in out Arr4T; I1, I2: in IT4; J1, J2: in IT3; K1, K2: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I1, I2, J1, J2, K1, K2)),
          Pre     => I1 /= I2 and J1 /= J2 and K1 /= K2,
          Post    => A = A'Old'Update (I1 => A'Old(I1)'Update (J1 => A'Old(I1)(J1)'Update (K1 => B)), I2 => A'Old(I2)'Update (J2 => A'Old(I2)(J2)'Update (K2 => C)));

  procedure TestD22
            (A: in out Arr4T; I1, I2: in IT4; J1, J2: in IT3; K1, K2: in IT2; B, C: in Arr1T)
     with Depends => (A =>+ (B, C, I1, I2, J1, J2, K1, K2)),
          Post    => (for all P in IT4 => (for all O in IT3 => (for all N in IT2 => (for all M in IT1 => (A(P)(O)(N)(M) in ET1)))));

  -----------------------------------------------
  -- [E] Simple record tests
  -----------------------------------------------
  procedure TestE01
	    (R: in out Rec1T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R = R'Old'Update (F1 => E);

  procedure TestE02
	    (R: in out Rec1T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R.F1 = E and R.G1 = R'Old.G1;

  procedure TestE03
	    (R: in out Rec1T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R = Rec1T'(F1 => E, G1 => R'Old.G1);

  procedure TestE04
	    (R: out Rec1T; E: in ET1; F: in ET2)
     with Depends => (R => (E, F)),
          Post    => R.F1 = E and R.G1 = F;

  procedure TestE05
	    (R: out Rec1T; E: in ET1; F: in ET2)
     with Depends => (R => (E, F)),
          Post    => R = Rec1T'(F1 => E, G1 => F);

  procedure TestE06
	    (R: in out Rec1T)
     with Depends => (R =>+ null),
          Pre     => R.F1 in ET2,
          Post    => R = R'Old'Update (F1 => R'Old.G1, G1 => R'Old.F1);

  procedure TestE07
	    (R: in out Rec1T)
     with Depends => (R =>+ null),
          Pre     => R.F1 in ET2,
          Post    => R.F1 = R'Old.G1 and R.G1 = R'Old.F1;

  procedure TestE08
	    (R: in out Rec1T)
     with Depends => (R =>+ null),
          Pre     => R.F1 in ET2,
          Post    => R = Rec1T'(F1 => R'Old.G1, G1 => R'Old.F1);

  procedure TestE09
	    (R: out Rec1T; S: in Rec1T)
     with Depends => (R => S),
          Post    => R = S'Update (F1 => 25);

  procedure TestE10
	    (R: out Rec1T; S: in Rec1T)
     with Depends => (R => S),
          Post    => R.F1 = 25 and R.G1 = S.G1;

  procedure TestE11
	    (R: out Rec1T; S: in Rec1T)
     with Depends => (R => S),
          Post    => R = Rec1T'(F1 => 25, G1 => S.G1);

  -----------------------------------------------
  -- [F] Simple record tests
  -----------------------------------------------
  procedure TestF01
	    (R: in out Rec2T; E: in ET2)
     with Depends => (R =>+ E),
          Post    => R = R'Old'Update (G2 => R'Old.G2'Update (G1 => E));

  procedure TestF02
	    (R: in out Rec2T; E: in ET2)
     with Depends => (R =>+ E),
          Post    => R.F2 = R'Old.F2 and R.H2 = R'Old.H2 and R.G2 = R'Old.G2'Update (G1 => E);

  procedure TestF03
	    (R: in out Rec2T; E: in ET2)
     with Depends => (R =>+ E),
          Post    => R.F2 = R'Old.F2 and R.H2 = R'Old.H2 and R.G2.F1 = R'Old.G2.F1 and R.G2.G1 = E;

  procedure TestF04
	    (R: in out Rec2T; E: in ET2)
     with Depends => (R =>+ E),
          Post    => R = Rec2T'(F2 => R'Old.F2, G2 => Rec1T'(F1 => R'Old.G2.F1, G1 => E), H2 => R'Old.H2);

  procedure TestF05
	    (R: in out Rec2T; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F)),
          Post    => R.F2 = R'Old.F2 and R.G2.F1 = E and R.G2.G1 = F and R.H2 = R'Old.H2;

  procedure TestF06
	    (R: in out Rec2T; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F)),
          Post    => R.F2 = R'Old.F2 and R.G2 = Rec1T'(F1 => E, G1 => F) and R.H2 = R'Old.H2;

  procedure TestF07
	    (R: in out Rec2T; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F)),
          Post    => R = Rec2T'(F2 => R'Old.F2, G2 => Rec1T'(F1 => E, G1 => F), H2 => R'Old.H2);

  procedure TestF08
	    (R: in out Rec2T; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F)),
          Post    => R = R'Update (G2 => Rec1T'(F1 => E, G1 => F));

  procedure TestF09
	    (R: in out Rec2T; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F)),
          Post    => R = R'Update (G2 => R'Old.G2'Update (F1 => E, G1 => F));

  procedure TestF10
	    (R: in out Rec2T)
     with Depends => (R =>+ null),
          Pre     => R.G2.F1 in ET2,
          Post    => R = R'Old'Update (G2 => R'Old.G2'Update (F1 => R'Old.G2.G1, G1 => R'Old.G2.F1));

  procedure TestF11
	    (R: in out Rec2T)
     with Depends => (R =>+ null),
          Pre     => R.G2.F1 in ET2,
          Post    => R.F2 = R'Old.F2 and R.G2.F1 = R'Old.G2.G1 and R.G2.G1 = R'Old.G2.F1 and R.H2 = R'Old.H2;

  procedure TestF12
	    (R: in out Rec2T)
     with Depends => (R =>+ null),
          Pre     => R.G2.F1 in ET2,
          Post    => R = R'Old'Update (G2 => Rec1T'(F1 => R'Old.G2.G1, G1 => R'Old.G2.F1));

  procedure TestF13
	    (R: in out Rec2T)
     with Depends => (R =>+ null),
          Pre     => R.G2.F1 in ET2,
          Post    => R = Rec2T'(F2 => R'Old.F2,  G2 => Rec1T'(F1 => R'Old.G2.G1, G1 => R'Old.G2.F1),  H2 => R'Old.H2);

  procedure TestF14
	    (R: in out Rec2T; A: in Rec1T)
     with Depends => (R =>+ A),
          Post    => R = R'Old'Update (G2 => A);

  procedure TestF15
	    (R: in out Rec2T; A: in Rec1T)
     with Depends => (R =>+ A),
          Post    => R.F2 = R'Old.F2 and R.G2 = A and R.H2 = R'Old.H2;

  procedure TestF16
	    (R: in out Rec2T; A: in Rec1T)
     with Depends => (R =>+ A),
          Post    => R.F2 = R'Old.F2 and R.G2.F1 = A.F1 and R.G2.G1 = A.G1 and R.H2 = R'Old.H2;

  procedure TestF17
	    (R: in out Rec2T; A: in Rec1T)
     with Depends => (R =>+ A),
          Post    => R = Rec2T'(F2 => R'Old.F2, G2 => A, H2 => R'Old.H2);

  procedure TestF18
	    (R: in out Rec2T; A: in Rec1T)
     with Depends => (R =>+ A),
          Post    => R = Rec2T'(F2 => R'Old.F2, G2 => Rec1T'(F1 => A.F1, G1 => A.G1), H2 => R'Old.H2);

  procedure TestF19
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R = R'Old'Update (G2 => A'Update (F1 => E));

  procedure TestF20
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R.F2 = R'Old.F2 and R.G2 = A'Update (F1 => E) and R.H2 = R'Old.H2;

  procedure TestF21
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R.F2 = R'Old.F2 and R.G2.F1 = E and R.G2.G1 = A.G1 and R.H2 = R'Old.H2;

  procedure TestF22
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R = Rec2T'(F2 => R'Old.F2, G2 => A'Update (F1 => E), H2 => R'Old.H2);

  procedure TestF23
	    (R: in out Rec2T; A: in Rec1T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R = Rec2T'(F2 => R'Old.F2, G2 => Rec1T'(F1 => E, G1 => A.G1), H2 => R'Old.H2);

  -----------------------------------------------
  -- [G] Record of record of record tests
  -----------------------------------------------
  procedure TestG01
	    (R: in out Rec3T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R = R'Old'Update (F3 => R'Old.F3'Update (G2 => R'Old.F3.G2'Update (F1 => E)));

  procedure TestG02
	    (R: in out Rec3T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R.G3 = R'Old.G3 and R.F3 = R'Old.F3'Update (G2 => R'Old.F3.G2'Update (F1 => E));

  procedure TestG03
	    (R: in out Rec3T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R.G3 = R'Old.G3 and R.F3.F2 = R'Old.F3.F2 and R.F3.H2 = R'Old.F3.H2 and R.F3.G2.F1 = E and R.F3.G2.G1 = R'Old.F3.G2.G1;

  procedure TestG04
	    (R: in out Rec3T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R = Rec3T'(F3 => Rec2T'(F2 => R'Old.F3.F2,  G2 => Rec1T'(F1 => E, G1 => R'Old.F3.G2.G1),  H2 => R'Old.F3.H2),  G3 => R'Old.G3);

  procedure TestG05
	    (R: in out Rec3T; E: in ET1; F: in ET3; G: in ET4)
     with Depends => (R =>+ (E, F, G)),
          Post    => R = R'Old'Update (F3 => R'Old.F3'Update (F2 => F, G2 => R'Old.F3.G2'Update (F1 => E), H2 => E1Tc), G3 => G);

  procedure TestG06
	    (R: in out Rec3T; E: in ET1; F: in ET3; G: in ET4)
     with Depends => (R =>+ (E, F, G)),
          Post    => R.G3 = G and R.F3 = R'Old.F3'Update (F2 => F, G2 => R'Old.F3.G2'Update (F1 => E), H2 => E1Tc);

  procedure TestG07
	    (R: in out Rec3T; E: in ET1; F: in ET3; G: in ET4)
     with Depends => (R =>+ (E, F, G)),
          Post    => R.G3 = G and R.F3.F2 = F and R.F3.H2 = E1Tc and R.F3.G2.F1 = E and R.F3.G2.G1 = R'Old.F3.G2.G1;

  procedure TestG08
	    (R: in out Rec3T; E: in ET1; F: in ET3; G: in ET4)
     with Depends => (R =>+ (E, F, G)),
          Post    => R = Rec3T'(F3 => Rec2T'(F2 => F,  G2 => Rec1T'(F1 => E, G1 => R'Old.F3.G2.G1),  H2 => E1Tc),  G3 => G);

  procedure TestG09
	    (R: in out Rec3T)
     with Depends => (R =>+ null),
          Pre     => R.F3.G2.F1 in ET2,
          Post    => R = R'Old'Update (F3 => R'Old.F3'Update (G2 => R'Old.F3.G2'Update (F1 => R'Old.F3.G2.G1, G1 => R'Old.F3.G2.F1)));

  procedure TestG10
	    (R: in out Rec3T)
     with Depends => (R =>+ null),
          Pre     => R.F3.G2.F1 in ET2,
          Post    => R.F3.F2 = R'Old.F3.F2 and R.F3.G2.F1 = R'Old.F3.G2.G1 and R.F3.G2.G1 = R'Old.F3.G2.F1 and R.F3.H2 = R'Old.F3.H2 and R.G3 = R'Old.G3;

  procedure TestG11
	    (R: in out Rec3T)
     with Depends => (R =>+ null),
          Pre     => R.F3.G2.F1 in ET2,
          Post    => R = R'Old'Update (F3 => R'Old.F3'Update (G2 => Rec1T'(F1 => R'Old.F3.G2.G1, G1 => R'Old.F3.G2.F1)));

  procedure TestG12
	    (R: in out Rec3T)
     with Depends => (R =>+ null),
          Pre     => R.F3.G2.F1 in ET2,
          Post    => R = Rec3T'(F3 => Rec2T'(F2 => R'Old.F3.F2,  G2 => Rec1T'(F1 => R'Old.F3.G2.G1, G1 => R'Old.F3.G2.F1),  H2 => R'Old.F3.H2),  G3 => R'Old.G3);

  procedure TestG13
	    (R: in out Rec3T; A: in Rec1T)
     with Depends => (R =>+ A),
          Post    => R = R'Old'Update (F3 => R'Old.F3'Update (G2 => A));

  procedure TestG14
	    (R: in out Rec3T; A: in Rec1T)
     with Depends => (R =>+ A),
          Post    => R.F3.F2 = R'Old.F3.F2 and R.F3.G2.F1 = A.F1 and R.F3.G2.G1 = A.G1 and R.F3.H2 = R'Old.F3.H2 and R.G3 = R'Old.G3;

  procedure TestG15
	    (R: in out Rec3T; A: in Rec1T)
     with Depends => (R =>+ A),
          Post    => R = R'Old'Update (F3 => R'Old.F3'Update (G2 => Rec1T'(F1 => A.F1, G1 => A.G1)));

  procedure TestG16
	    (R: in out Rec3T; A: in Rec1T)
     with Depends => (R =>+ A),
          Post    => R = Rec3T'(F3 => Rec2T'(F2 => R'Old.F3.F2,  G2 => Rec1T'(F1 => A.F1, G1 => A.G1),  H2 => R'Old.F3.H2),  G3 => R'Old.G3);

  procedure TestG17
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R = R'Old'Update (F3 => A'Update (G2 => A.G2'Update (F1 => E)));

  procedure TestG18
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R.F3 = A'Update (G2 => A.G2'Update (F1 => E)) and R.G3 = R'Old.G3;

  procedure TestG19
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R.F3.F2 = A.F2 and R.F3.G2.F1 = E and R.F3.G2.G1 = A.G2.G1 and R.F3.H2 = A.H2 and R.G3 = R'Old.G3;

  procedure TestG20
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R = Rec3T'(F3 => A'Update (G2 => A.G2'Update (F1 => E)), G3 => R'Old.G3);

  procedure TestG21
	    (R: in out Rec3T; A: in Rec2T; E: in ET1)
     with Depends => (R =>+ (A, E)),
          Post    => R = Rec3T'(F3 => Rec2T'(F2 => A.F2,  G2 => Rec1T'(F1 => E, G1 => A.G2.G1),  H2 => A.H2),  G3 => R'Old.G3);

  procedure TestG22
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
     with Depends => (R =>+ (A, B)),
          Post    => R = R'Old'Update (F3 => A'Update (G2 => B));

  procedure TestG23
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
     with Depends => (R =>+ (A, B)),
          Post    => R.F3 = A'Update (G2 => B) and R.G3 = R'Old.G3;

  procedure TestG24
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
     with Depends => (R =>+ (A, B)),
          Post    => R.F3.F2 = A.F2 and R.F3.G2.F1 = B.F1 and R.F3.G2.G1 = B.G1 and R.F3.H2 = A.H2 and R.G3 = R'Old.G3;

  procedure TestG25
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
     with Depends => (R =>+ (A, B)),
          Post    => R = Rec3T'(F3 => A'Update (G2 => B), G3 => R'Old.G3);

  procedure TestG26
	    (R: in out Rec3T; A: in Rec2T; B: in Rec1T)
     with Depends => (R =>+ (A, B)),
          Post    => R = Rec3T'(F3 => Rec2T'(F2 => A.F2,  G2 => Rec1T'(F1 => B.F1, G1 => B.G1),  H2 => A.H2),  G3 => R'Old.G3);

  -----------------------------------------------
  -- [H] Record of record of record of record tests
  -----------------------------------------------
  procedure TestH01
	    (R: in out Rec4T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R = R'Old'Update (F4 => R'Old.F4'Update (F3 => R'Old.F4.F3'Update (G2 => R'Old.F4.F3.G2'Update (F1 => E))));

  procedure TestH02
	    (R: in out Rec4T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R.F4 = R'Old.F4'Update (F3 => R'Old.F4.F3'Update (G2 => R'Old.F4.F3.G2'Update (F1 => E))) and R.G4 = R'Old.G4;

  procedure TestH03
	    (R: in out Rec4T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R.G4 = R'Old.G4 and R.F4.F3.F2 = R'Old.F4.F3.F2 and R.F4.F3.H2 = R'Old.F4.F3.H2 and R.F4.F3.G2.F1 = E and R.F4.F3.G2.G1 = R'Old.F4.F3.G2.G1 and R.F4.G3 = R'Old.F4.G3;

  procedure TestH04
	    (R: in out Rec4T; E: in ET1)
     with Depends => (R =>+ E),
          Post    => R = Rec4T'(F4 => Rec3T'(F3 => Rec2T'(F2 => R'Old.F4.F3.F2,  G2 => Rec1T'(F1 => E,  G1 => R'Old.F4.F3.G2.G1),  H2 => R'Old.F4.F3.H2),  G3 => R'Old.F4.G3),  G4 => R'Old.G4);

  procedure TestH05
	    (R: in out Rec4T; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F)),
          Post    => R = R'Old'Update (F4 => R'Old.F4'Update (F3 => R'Old.F4.F3'Update (G2 => R'Old.F4.F3.G2'Update (F1 => E, G1 => F))));

  procedure TestH06
	    (R: in out Rec4T; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F)),
          Post    => R.F4 = R'Old.F4'Update (F3 => R'Old.F4.F3'Update (G2 => R'Old.F4.F3.G2'Update (F1 => E, G1 => F))) and R.G4 = R'Old.G4;

  procedure TestH07
	    (R: in out Rec4T; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F)),
          Post    => R.G4 = R'Old.G4 and R.F4.F3.F2 = R'Old.F4.F3.F2 and R.F4.F3.H2 = R'Old.F4.F3.H2 and R.F4.F3.G2.F1 = E and R.F4.F3.G2.G1 = F and R.F4.G3 = R'Old.F4.G3;

  procedure TestH08
	    (R: in out Rec4T; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F)),
          Post    => R = Rec4T'(F4 => Rec3T'(F3 => Rec2T'(F2 => R'Old.F4.F3.F2,  G2 => Rec1T'(F1 => E, G1 => F),  H2 => R'Old.F4.F3.H2),  G3 => R'Old.F4.G3),  G4 => R'Old.G4);

  procedure TestH09
	    (R: in out Rec4T)
     with Depends => (R =>+ null),
          Pre     => R.G4 in Enum1TA,
          Post    => R = R'Old'Update (F4 => R'Old.F4'Update (F3 => R'Old.F4.F3'Update (H2 => R'Old.G4)), G4 => R'Old.F4.F3.H2);

  procedure TestH10
	    (R: in out Rec4T)
     with Depends => (R =>+ null),
          Pre     => R.G4 in Enum1TA,
          Post    => R.F4.F3.F2 = R'Old.F4.F3.F2 and R.F4.F3.G2.F1 = R'Old.F4.F3.G2.F1 and R.F4.F3.G2.G1 = R'Old.F4.F3.G2.G1 and R.F4.F3.H2 = R'Old.G4 and R.F4.G3 = R'Old.F4.G3 and R.G4 = R'Old.F4.F3.H2;

  procedure TestH11
	    (R: in out Rec4T)
     with Depends => (R =>+ null),
          Pre     => R.G4 in Enum1TA,
          Post    => R = R'Old'Update (F4 => R'Old.F4'Update (F3 => Rec2T'(F2 => R'Old.F4.F3.F2,  G2 => R'Old.F4.F3.G2,  H2 => R'Old.G4)), G4 => R'Old.F4.F3.H2);

  procedure TestH12
	    (R: in out Rec4T)
     with Depends => (R =>+ null),
          Pre     => R.G4 in Enum1TA,
          Post    => R = Rec4T'(F4 => Rec3T'(F3 => Rec2T'(F2 => R'Old.F4.F3.F2,  G2 => Rec1T'(F1 => R'Old.F4.F3.G2.F1,  G1 => R'Old.F4.F3.G2.G1),  H2 => R'Old.G4),  G3 => R'Old.F4.G3),  G4 => R'Old.F4.F3.H2);

  procedure TestH13
	    (R: in out Rec4T)
     with Depends => (R =>+ null),
          Pre     => R.G4 in Enum1TA,
          Post    => R = R'Old'Update (F4 => R'Old.F4'Update (F3 => R'Old.F4.F3'Update (H2 => R'Old.G4)), G4 => R'Old.F4.F3.H2);

  procedure TestH14
	    (R: in out Rec4T)
     with Depends => (R =>+ null),
          Pre     => R.G4 in Enum1TA,
          Post    => R.F4.F3.F2 = R'Old.F4.F3.F2 and R.F4.F3.G2.F1 = R'Old.F4.F3.G2.F1 and R.F4.F3.G2.G1 = R'Old.F4.F3.G2.G1 and R.F4.F3.H2 = R'Old.G4 and R.F4.G3 = R'Old.F4.G3 and R.G4 = R'Old.F4.F3.H2;

  procedure TestH15
	    (R: in out Rec4T)
     with Depends => (R =>+ null),
          Pre     => R.G4 in Enum1TA,
          Post    => R = R'Old'Update (F4 => R'Old.F4'Update (F3 => Rec2T'(F2 => R'Old.F4.F3.F2,  G2 => R'Old.F4.F3.G2,  H2 => R'Old.G4)), G4 => R'Old.F4.F3.H2);

  procedure TestH16
	    (R: in out Rec4T)
     with Depends => (R =>+ null),
          Pre     => R.G4 in Enum1TA,
          Post    => R = Rec4T'(F4 => Rec3T'(F3 => Rec2T'(F2 => R'Old.F4.F3.F2,  G2 => Rec1T'(F1 => R'Old.F4.F3.G2.F1,  G1 => R'Old.F4.F3.G2.G1),  H2 => R'Old.G4),  G3 => R'Old.F4.G3),  G4 => R'Old.F4.F3.H2);

  procedure TestH17
	    (R: in out Rec4T; A: in Rec3T; B: in Rec2T; C: in Rec1T; D: in ET1)
     with Depends => (R =>+ (A, B, C, D)),
          Post    => R = R'Old'Update (F4 => A'Update (F3 => B'Update (G2 => C'Update (F1 => D))));

  procedure TestH18
	    (R: in out Rec4T; A: in Rec3T; B: in Rec2T; C: in Rec1T; D: in ET1)
     with Depends => (R =>+ (A, B, C, D)),
          Post    => R.F4.F3.F2 = B.F2 and R.F4.F3.G2.F1 = D and R.F4.F3.G2.G1 = C.G1 and R.F4.F3.H2 = B.H2 and R.F4.G3 = A.G3 and R.G4 = R'Old.G4;

  procedure TestH19
	    (R: in out Rec4T; A: in Rec3T; B: in Rec2T; C: in Rec1T; D: in ET1)
     with Depends => (R =>+ (A, B, C, D)),
          Post    => R = R'Old'Update (F4 => A'Update (F3 => B'Update (G2 => Rec1T'(F1 => D, G1 => C.G1))));

  procedure TestH20
	    (R: in out Rec4T; A: in Rec3T; B: in Rec2T; C: in Rec1T; D: in ET1)
     with Depends => (R =>+ (A, B, C, D)),
          Post    => R = Rec4T'(F4 => Rec3T'(F3 => Rec2T'(F2 => B.F2,  G2 => Rec1T'(F1 => D, G1 => C.G1),  H2 => B.H2),  G3 => A.G3),  G4 => R'Old.G4);

  -----------------------------------------------
  -- [I] Mixed nested record tests
  -----------------------------------------------
  procedure TestI01
	    (R: in out Rec5T; A, B: in Rec1T)
     with Depends => (R =>+ (A, B)),
          Post    => R = R'Old'Update (F5 => R'Old.F5'Update (G2 => A), H5 => B);

  procedure TestI02
	    (R: in out Rec5T; A, B: in Rec1T)
     with Depends => (R =>+ (A, B)),
          Post    => R.F5.F2 = R'Old.F5.F2 and R.F5.G2.F1 = A.F1 and R.F5.G2.G1 = A.G1 and R.F5.H2 = R'Old.F5.H2 and R.G5 = R'Old.G5 and R.H5.F1 = B.F1 and R.H5.G1 = B.G1;

  procedure TestI03
	    (R: in out Rec5T; A, B: in Rec1T)
     with Depends => (R =>+ (A, B)),
          Post    => R = R'Old'Update (F5 => Rec2T'(F2 => R'Old.F5.F2, G2 => A, H2 => R'Old.F5.H2), H5 => B);

  procedure TestI04
	    (R: in out Rec5T; A, B: in Rec1T)
     with Depends => (R =>+ (A, B)),
          Post    => R = Rec5T'(F5 => Rec2T'(F2 => R'Old.F5.F2, G2 => A, H2 => R'Old.F5.H2),  G5 => R'Old.G5,  H5 => B);

  procedure TestI05
	    (R: in out Rec5T)
     with Depends => (R =>+ null),
          Post    => R = R'Old'Update (F5 => R'Old.F5'Update (G2 => R'Old.H5), H5 => R'Old.F5.G2);

  procedure TestI06
	    (R: in out Rec5T)
     with Depends => (R =>+ null),
          Post    => R.F5.F2 = R'Old.F5.F2 and R.F5.G2.F1 = R'Old.H5.F1 and R.F5.G2.G1 = R'Old.H5.G1 and R.F5.H2 = R'Old.F5.H2 and R.G5 = R'Old.G5 and R.H5.F1 = R'Old.F5.G2.F1 and R.H5.G1 = R'Old.F5.G2.G1;

  procedure TestI07
	    (R: in out Rec5T)
     with Depends => (R =>+ null),
          Post    => R = R'Old'Update (F5 => Rec2T'(F2 => R'Old.F5.F2, G2 => R'Old.H5, H2 => R'Old.F5.H2), H5 => R'Old.F5.G2);

  procedure TestI08
	    (R: in out Rec5T)
     with Depends => (R =>+ null),
          Post    => R = Rec5T'(F5 => Rec2T'(F2 => R'Old.F5.F2, G2 => R'Old.H5, H2 => R'Old.F5.H2),  G5 => R'Old.G5,  H5 => R'Old.F5.G2);

  procedure TestI09
	    (R: in out Rec5T)
     with Depends => (R =>+ null),
          Post    => R = R'Old'Update (F5 => R'Old.F5'Update (G2 => R'Old.H5), H5 => R'Old.F5.G2);

  procedure TestI10
	    (R: in out Rec5T)
     with Depends => (R =>+ null),
          Post    => R.F5.F2 = R'Old.F5.F2 and R.F5.G2.F1 = R'Old.H5.F1 and R.F5.G2.G1 = R'Old.H5.G1 and R.F5.H2 = R'Old.F5.H2 and R.G5 = R'Old.G5 and R.H5.F1 = R'Old.F5.G2.F1 and R.H5.G1 = R'Old.F5.G2.G1;

  procedure TestI11
	    (R: in out Rec5T)
     with Depends => (R =>+ null),
          Post    => R = R'Old'Update (F5 => Rec2T'(F2 => R'Old.F5.F2, G2 => R'Old.H5, H2 => R'Old.F5.H2), H5 => R'Old.F5.G2);

  procedure TestI12
	    (R: in out Rec5T)
     with Depends => (R =>+ null),
          Post    => R = Rec5T'(F5 => Rec2T'(F2 => R'Old.F5.F2, G2 => R'Old.H5, H2 => R'Old.F5.H2),  G5 => R'Old.G5,  H5 => R'Old.F5.G2);

  -----------------------------------------------
  -- [J] Array(1) of record(1)
  -----------------------------------------------
  procedure TestJ01
	    (A: in out AofR1; I: in IT1; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => (for all N in IT1 => (A(N) in Rec1T and A(N).F1 in ET1 and A(N).G1 in ET2));

  procedure TestJ02
	    (A: in out AofR1; I: in IT1; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => (for all N in IT1 => (if N /= I then (A (N) = A'Old (N)))) and A (I) .F1 = F and A (I) .G1 = A'Old (I) .G1;

  procedure TestJ03
	    (A: in out AofR1; I: in IT1; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => A = A'Old'Update (I => A'Old(I)'Update (F1 => F));

  procedure TestJ04
	    (A: in out AofR1; I: in IT1; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => (for all N in IT1 => (A(N).F1 in ET1)) and (for all N in IT1 => (A(N).G1 in ET2));

  procedure TestJ05
	    (A: in out AofR1; I, J: in IT1; F, G: in ET1)
     with Depends => (A =>+ (F, G, I, J)),
          Pre     => I /= J,
          Post    => (for all N in IT1 => (A(N) in Rec1T and A(N).F1 in ET1 and A(N).G1 in ET2));

  procedure TestJ06
	    (A: in out AofR1; I, J: in IT1; F, G: in ET1)
     with Depends => (A =>+ (F, G, I, J)),
          Pre     => I /= J,
          Post    => (for all N in IT1 => (if (N /= I and N /= J) then (A (N) = A'Old (N)))) and A (I) .F1 = F and A (I) .G1 = A'Old (I) .G1 and A (J) .F1 = G and A (J) .G1 = A'Old (J) .G1;

  procedure TestJ07
	    (A: in out AofR1; I, J: in IT1; F, G: in ET1)
     with Depends => (A =>+ (F, G, I, J)),
          Pre     => I /= J,
          Post    => A = A'Old'Update (I => A'Old(I)'Update (F1 => F), J => A'Old(J)'Update (F1 => G));

  procedure TestJ08
	    (A: in out AofR1; I, J: in IT1; F, G: in ET1)
     with Depends => (A =>+ (F, G, I, J)),
          Pre     => I /= J,
          Post    => (for all N in IT1 => (A(N).F1 in ET1)) and (for all N in IT1 => (A(N).G1 in ET2));

  procedure TestJ09
	    (A: in out AofR1; I, J: in IT1)
     with Depends => (A =>+ (I, J)),
          Post    => (for all N in IT1 => (A(N) in Rec1T and A(N).F1 in ET1 and A(N).G1 in ET2));

  procedure TestJ10
	    (A: in out AofR1; I, J: in IT1)
     with Depends => (A =>+ (I, J)),
          Post    => (for all N in IT1 => (if (N /= I and N /= J) then (A (N) = A'Old (N)))) and A (I) .G1 = A'Old (J) .G1 and A (J) .G1 = A'Old (I) .G1 and A (I) .F1 = A'Old (I) .F1 and A (J) .F1 = A'Old (J) .F1;

  procedure TestJ11
	    (A: in out AofR1; I, J: in IT1)
     with Depends => (A =>+ (I, J)),
          Post    => A = A'Old'Update (I => A'Old (I) 'Update (G1 => A'Old (J) .G1), J => A'Old (J) 'Update (G1 => A'Old (I) .G1)) and (if I = J then A = A'Old);

  procedure TestJ12
	    (A: in out AofR1; I, J: in IT1)
     with Depends => (A =>+ (I, J)),
          Post    => (for all N in IT1 => (A(N).F1 in ET1)) and (for all N in IT1 => (A(N).G1 in ET2));

  procedure TestJ13
	    (A: in out AofR1; I: in IT1; R: in Rec1T)
     with Depends => (A =>+ (I, R)),
          Post    => (for all N in IT1 => (A(N) in Rec1T and A(N).F1 in ET1 and A(N).G1 in ET2));

  procedure TestJ14
	    (A: in out AofR1; I: in IT1; R: in Rec1T)
     with Depends => (A =>+ (I, R)),
          Post    => (for all N in IT1 => (if N /= I then (A (N) = A'Old (N)))) and A (I) = R and A (I) .F1 = R.F1 and A (I) .G1 = R.G1;

  procedure TestJ15
	    (A: in out AofR1; I: in IT1; R: in Rec1T)
     with Depends => (A =>+ (I, R)),
          Post    => A = A'Old'Update (I => R);

  procedure TestJ16
	    (A: in out AofR1; I: in IT1; R: in Rec1T)
     with Depends => (A =>+ (I, R)),
          Post    => (for all N in IT1 => (A(N).F1 in ET1)) and (for all N in IT1 => (A(N).G1 in ET2));

  procedure TestJ17
	    (A: in out AofR1; I: in IT1; R: in Rec1T; E: ET1)
     with Depends => (A =>+ (E, I, R)),
          Post    => (for all N in IT1 => (A(N) in Rec1T and A(N).F1 in ET1 and A(N).G1 in ET2));

  procedure TestJ18
	    (A: in out AofR1; I: in IT1; R: in Rec1T; E: ET1)
     with Depends => (A =>+ (E, I, R)),
          Post    => (for all N in IT1 => (if N /= I then (A (N) = A'Old (N)))) and A (I) = R'Update (F1 => E) and A (I) .F1 = E and A (I) .G1 = R.G1;

  procedure TestJ19
	    (A: in out AofR1; I: in IT1; R: in Rec1T; E: ET1)
     with Depends => (A =>+ (E, I, R)),
          Post    => A = A'Old'Update (I => R'Update (F1 => E));

  procedure TestJ20
	    (A: in out AofR1; I: in IT1; R: in Rec1T; E: ET1)
     with Depends => (A =>+ (E, I, R)),
          Post    => (for all N in IT1 => (A(N).F1 in ET1)) and (for all N in IT1 => (A(N).G1 in ET2));

  -----------------------------------------------
  -- [K] Array(1) of record(2)
  -----------------------------------------------
  procedure TestK01
	    (A: in out AofR2; I: in IT2; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => (for all N in IT2 => (A(N) in Rec2T and A(N).F2 in ET3 and A(N).H2 in Enum1TA and A(N).G2 in Rec1T and A(N).G2.F1 in ET1 and A(N).G2.G1 in ET2));

  procedure TestK02
	    (A: in out AofR2; I: in IT2; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => (for all N in IT2 => (if N /= I then (A (N) = A'Old (N)))) and A (I) .G2.F1 = F and A (I) .G2.G1 = A'Old (I) .G2.G1 and A (I) .F2 = A'Old (I) .F2 and A (I) .H2 = A'Old (I) .H2;

  procedure TestK03
	    (A: in out AofR2; I: in IT2; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => A = A'Old'Update (I => A'Old(I)'Update (G2 => A'Old(I).G2'Update (F1 => F)));

  procedure TestK04
	    (A: in out AofR2; I: in IT2; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => (for all N in IT2 => (A(N).F2 in ET3)) and (for all N in IT2 => (A(N).H2 in Enum1TA)) and (for all N in IT2 => (A(N).G2.F1 in ET1)) and (for all N in IT2 => (A(N).G2.G1 in ET2));

  procedure TestK05
	    (A: in out AofR2; I: in IT2; E: in ET3; F: in ET1; G: in ET2; H: in Enum1TA)
     with Depends => (A =>+ (E, F, G, H, I)),
          Post    => (for all N in IT2=> (A(N) in Rec2T and A(N).F2 in ET3 and A(N).H2 in Enum1TA and A(N).G2 in Rec1T and A(N).G2.F1 in ET1 and A(N).G2.G1 in ET2));

  procedure TestK06
	    (A: in out AofR2; I: in IT2; E: in ET3; F: in ET1; G: in ET2; H: in Enum1TA)
     with Depends => (A =>+ (E, F, G, H, I)),
          Post    => (for all N in IT2 => (if N /= I then (A (N) = A'Old (N)))) and A (I) .F2 = E and A (I) .G2.F1 = F and A (I) .G2.G1 = G and A (I) .H2 = H;

  procedure TestK07
	    (A: in out AofR2; I: in IT2; E: in ET3; F: in ET1; G: in ET2; H: in Enum1TA)
     with Depends => (A =>+ (E, F, G, H, I)),
          Post    => A = A'Old'Update (I => Rec2T'(F2 => E, G2 => Rec1T'(F1 => F, G1 => G), H2 => H));

  procedure TestK08
	    (A: in out AofR2; I: in IT2; E: in ET3; F: in ET1; G: in ET2; H: in Enum1TA)
     with Depends => (A =>+ (E, F, G, H, I)),
          Post    => (for all N in IT2 => (A(N).F2 in ET3)) and (for all N in IT2 => (A(N).H2 in Enum1TA)) and (for all N in IT2 => (A(N).G2.F1 in ET1)) and (for all N in IT2 => (A(N).G2.G1 in ET2));

  -----------------------------------------------
  -- [L] Array(1) of record(3)
  -----------------------------------------------
  procedure TestL01
	    (A: in out AofR3; I: in IT3; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => (for all N in IT3 => (A(N) in Rec3T and A(N).F3 in Rec2T and A(N).F3.F2 in ET3 and A(N).F3.H2 in Enum1TA and A(N).F3.G2 in Rec1T and A(N).F3.G2.F1 in ET1 and A(N).F3.G2.G1 in ET2 and A(N).G3 in ET4));

  procedure TestL02
	    (A: in out AofR3; I: in IT3; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => (for all N in IT3 => (if N /= I then (A (N) = A'Old (N)))) and A (I) .F3.G2.F1 = F and A (I) .F3.G2.G1 = A'Old (I) .F3.G2.G1 and A (I) .F3.F2 = A'Old (I) .F3.F2 and A (I) .F3.H2 = A'Old (I) .F3.H2 and A (I) .G3 = A'Old (I) .G3;

  procedure TestL03
	    (A: in out AofR3; I: in IT3; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => A = A'Old'Update (I => A'Old(I)'Update (F3 => A'Old(I).F3'Update (G2 => A'Old(I).F3.G2'Update (F1 => F))));

  procedure TestL04
	    (A: in out AofR3; I: in IT3; F: in ET1)
     with Depends => (A =>+ (F, I)),
          Post    => (for all N in IT3 => (A(N).F3.F2 in ET3)) and (for all N in IT3 => (A(N).F3.H2 in Enum1TA)) and (for all N in IT3 => (A(N).F3.G2.F1 in ET1)) and (for all N in IT3 => (A(N).F3.G2.G1 in ET2)) and (for all N in IT3 => (A(N).G3 in ET4));

  procedure TestL05
	    (A: in out AofR3; I: in IT3; D: in ET4; E: in ET3; F: in ET1; G: in ET2;
	     H: in Enum1TA)
     with Depends => (A =>+ (D, E, F, G, H, I)),
          Post    => (for all N in IT3 => (A(N) in Rec3T and A(N).F3 in Rec2T and A(N).F3.F2 in ET3 and A(N).F3.H2 in Enum1TA and A(N).F3.G2 in Rec1T and A(N).F3.G2.F1 in ET1 and A(N).F3.G2.G1 in ET2 and A(N).G3 in ET4));

  procedure TestL06
	    (A: in out AofR3; I: in IT3; D: in ET4; E: in ET3; F: in ET1; G: in ET2;
	     H: in Enum1TA)
     with Depends => (A =>+ (D, E, F, G, H, I)),
          Post    => (for all N in IT3 => (if N /= I then (A (N) = A'Old (N)))) and A (I) .G3 = D and A (I) .F3.F2 = E and A (I) .F3.G2.F1 = F and A (I) .F3.G2.G1 = G and A (I) .F3.H2 = H;

  procedure TestL07
	    (A: in out AofR3; I: in IT3; D: in ET4; E: in ET3; F: in ET1; G: in ET2;
	     H: in Enum1TA)
     with Depends => (A =>+ (D, E, F, G, H, I)),
          Post    => A = A'Old'Update (I => Rec3T'(F3 => Rec2T'(F2 => E, G2 => Rec1T'(F1 => F, G1 => G), H2 => H),  G3 => D));

  procedure TestL08
	    (A: in out AofR3; I: in IT3; D: in ET4; E: in ET3; F: in ET1; G: in ET2;
	     H: in Enum1TA)
     with Depends => (A =>+ (D, E, F, G, H, I)),
          Post    => (for all N in IT3 => (A(N).F3.F2 in ET3)) and (for all N in IT3 => (A(N).F3.H2 in Enum1TA)) and (for all N in IT3 => (A(N).F3.G2.F1 in ET1)) and (for all N in IT3 => (A(N).F3.G2.G1 in ET2)) and (for all N in IT3 => (A(N).G3 in ET4));

  -----------------------------------------------
  -- [M] Array(1) of record(mixed)
  -----------------------------------------------
  procedure TestM01
	    (A: in out AofR4; I: in IT4; F, G: in ET1)
     with Depends => (A =>+ (F, G, I)),
          Post    => (for all N in IT4 => (A(N) in Rec5T and A(N).F5 in Rec2T and A(N).F5.F2 in ET3 and A(N).F5.H2 in Enum1TA and A(N).F5.G2 in Rec1T and A(N).F5.G2.F1 in ET1 and A(N).F5.G2.G1 in ET2 and A(N).G5 in Boolean and A(N).H5 in Rec1T and A(N).H5.F1 in ET1 and A(N).H5.G1 in ET2));

  procedure TestM02
	    (A: in out AofR4; I: in IT4; F, G: in ET1)
     with Depends => (A =>+ (F, G, I)),
          Post    => (for all N in IT4 => (if N /= I then (A (N) = A'Old (N)))) and A (I) .F5.G2.F1 = F and A (I) .F5.G2.G1 = A'Old (I) .F5.G2.G1 and A (I) .F5.F2 = A'Old (I) .F5.F2 and A (I) .F5.H2 = A'Old (I) .F5.H2 and A (I) .G5 = A'Old (I) .G5 and A (I) .H5.F1 = G and A (I) .H5.G1 = A'Old (I) .H5.G1;

  procedure TestM03
	    (A: in out AofR4; I: in IT4; F, G: in ET1)
     with Depends => (A =>+ (F, G, I)),
          Post    => A = A'Old'Update (I => A'Old(I)'Update (F5 => A'Old(I).F5'Update (G2 => A'Old(I).F5.G2'Update (F1 => F)), H5 => A'Old(I).H5'Update (F1 => G)));

  procedure TestM04
	    (A: in out AofR4; I: in IT4; F, G: in ET1)
     with Depends => (A =>+ (F, G, I)),
          Post    => (for all N in IT4 => (A(N).F5.F2 in ET3)) and (for all N in IT4 => (A(N).F5.H2 in Enum1TA)) and (for all N in IT4 => (A(N).F5.G2.F1 in ET1)) and (for all N in IT4 => (A(N).F5.G2.G1 in ET2)) and (for all N in IT4 => (A(N).G5 in Boolean)) and (for all N in IT4 => (A(N).H5.F1 in ET1)) and (for all N in IT4 => (A(N).H5.G1 in ET2));

  -----------------------------------------------
  -- [N] Record(1) of array(1)
  -----------------------------------------------
  procedure TestN01
	    (R: in out RofA1; I: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => (for all N in IT1 => (R.S1(N) in ET1)) and R.T1 in Enum2T;

  procedure TestN02
	    (R: in out RofA1; I: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => (for all N in IT1 => (if N /= I then R.S1 (N) = R'Old.S1 (N))) and R.S1 (I) = E and R.T1 = R'Old.T1;

  procedure TestN03
	    (R: in out RofA1; I: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => R = R'Old'Update (S1 => R'Old.S1'Update (I => E));

  procedure TestN04
	    (R: in out RofA1; I: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => R.S1 = R'Old.S1'Update (I => E) and R.T1 = R'Old.T1;

  procedure TestN05
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
     with Depends => (R =>+ (E, F, I)),
          Post    => (for all N in IT1 => (R.S1(N) in ET1)) and R.T1 in Enum2T;

  procedure TestN06
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
     with Depends => (R =>+ (E, F, I)),
          Post    => (for all N in IT1 => (if N /= I then R.S1 (N) = R'Old.S1 (N))) and R.S1 (I) = E and R.T1 = F;

  procedure TestN07
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
     with Depends => (R =>+ (E, F, I)),
          Post    => R = R'Old'Update (S1 => R'Old.S1'Update (I => E), T1 => F);

  procedure TestN08
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
     with Depends => (R =>+ (E, F, I)),
          Post    => R.S1 = R'Old.S1'Update (I => E) and R.T1 = F;

  procedure TestN09
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
     with Depends => (R =>+ (E, F, I)),
          Post    => (for all N in IT1 => (R.S1(N) in ET1)) and R.T1 in Enum2T;

  procedure TestN10
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
     with Depends => (R =>+ (E, F, I)),
          Post    => (for all N in IT1 => (if N /= I then R.S1 (N) = R'Old.S1 (N))) and R.S1 (I) = E and R.T1 = F;

  procedure TestN11
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
     with Depends => (R =>+ (E, F, I)),
          Post    => R = R'Old'Update (S1 => R'Old.S1'Update (I => E), T1 => F);

  procedure TestN12
	    (R: in out RofA1; I: in IT1; E: in ET1; F: in Enum2T)
     with Depends => (R =>+ (E, F, I)),
          Post    => R.S1 = R'Old.S1'Update (I => E) and R.T1 = F;

  procedure TestN13
	    (R: in out RofA1; I, J: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I, J)),
          Post    => (for all N in IT1 => (R.S1(N) in ET1)) and R.T1 in Enum2T;

  procedure TestN14
	    (R: in out RofA1; I, J: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I, J)),
          Pre     => I /= J,
          Post    => (for all N in IT1 => (if (N /= I and N /= J) then R.S1 (N) = R'Old.S1 (N))) and R.S1 (I) = E and R.S1 (J) = F and R.T1 = R'Old.T1;

  procedure TestN15
	    (R: in out RofA1; I, J: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I, J)),
          Pre     => I /= J,
          Post    => R = R'Old'Update (S1 => R'Old.S1'Update (I => E, J => F));

  procedure TestN16
	    (R: in out RofA1; I, J: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I, J)),
          Pre     => I /= J,
          Post    => R.S1 = R'Old.S1'Update (I => E, J => F) and R.T1 = R'Old.T1;

  procedure TestN17
	    (R: out RofA1; A: in Arr1T; E: in Enum2T)
     with Depends => (R => (A, E)),
          Post    => (for all N in IT1 => (R.S1(N) in ET1)) and R.T1 in Enum2T;

  procedure TestN18
	    (R: out RofA1; A: in Arr1T; E: in Enum2T)
     with Depends => (R => (A, E)),
          Post    => (for all N in IT1 => (R.S1(N) = A(N))) and R.S1 = A and R.T1 = E;

  procedure TestN19
	    (R: out RofA1; A: in Arr1T; E: in Enum2T)
     with Depends => (R => (A, E)),
          Post    => R = RofA1'(S1 => A, T1 => E);

  -----------------------------------------------
  -- [O] Record(1) of array(2)
  -----------------------------------------------
  procedure TestO01
	    (R: in out RofA2; I: in IT2; J: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J)),
          Post    => (for all M in IT2 => (for all N in IT1 => (R.S2(M)(N) in ET1))) and R.T2 in Boolean;

  procedure TestO02
	    (R: in out RofA2; I: in IT2; J: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J)),
          Post    => (for all M in IT2 => (for all N in IT1 => (if (M /= I or N /= J) then R.S2 (M) (N) = R'Old.S2 (M) (N)))) and R.S2 (I) (J) = E and R.T2 = R'Old.T2;

  procedure TestO03
	    (R: in out RofA2; I: in IT2; J: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J)),
          Post    => R = R'Old'Update (S2 => R'Old.S2'Update (I => R'Old.S2(I)'Update (J => E)));

  procedure TestO04
	    (R: in out RofA2; I: in IT2; J: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J)),
          Post    => R.S2 = R'Old.S2'Update (I => R'Old.S2(I)'Update (J => E)) and R.T2 = R'Old.T2;

  procedure TestO05
	    (R: in out RofA2; I1, I2: in IT2; J1, J2: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I1, I2, J1, J2)),
          Post    => (for all M in IT2 => (for all N in IT1 => (R.S2(M)(N) in ET1))) and R.T2 in Boolean;

  procedure TestO06
	    (R: in out RofA2; I1, I2: in IT2; J1, J2: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I1, I2, J1, J2)),
          Pre     => I1 /= I2 or J1 /= J2,
          Post    => (for all N in IT1 => (for all M in IT2 => (if ((M /= I1 or N /= J1) and (M /= I2 or N /= J2)) then R.S2 (M) (N) = R'Old.S2 (M) (N)))) and R.S2 (I1) (J1) = E and R.S2 (I2) (J2) = F and R.T2 = R'Old.T2;

  procedure TestO07
	    (R: in out RofA2; I1, I2: in IT2; J1, J2: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I1, I2, J1, J2)),
          Pre     => I1 /= I2 or J1 /= J2,
          Post    => (if I1 /= I2 then R = R'Old'Update (S2 => R'Old.S2'Update (I1 => R'Old.S2 (I1) 'Update (J1 => E), I2 => R'Old.S2 (I2) 'Update (J2 => F)))) and (if I1 = I2 then R = R'Old'Update (S2 => R'Old.S2'Update (I1 => R'Old.S2 (I1) 'Update (J1 => E, J2 => F))));

  procedure TestO08
	    (R: in out RofA2; I: in IT2; A: in Arr1T)
     with Depends => (R =>+ (A, I)),
          Post    => (for all M in IT2 => (for all N in IT1 => (R.S2(M)(N) in ET1))) and R.T2 in Boolean;

  procedure TestO09
	    (R: in out RofA2; I: in IT2; A: in Arr1T)
     with Depends => (R =>+ (A, I)),
          Post    => R.S2 (I) = A and R.S2 (55-I) (1) = 0 and R.T2 = R'Old.T2 and (for all M in IT2 => (if (M /= I and M /= 55-I) then R.S2 (M) = R'Old.S2 (M))) and (for all N in IT1 => (R.S2 (I) (N) = A (N))) and (for all N in IT1 range 2..IT1'Last => (R.S2 (55-I) (N) = R'Old.S2 (55-I) (N)));

  procedure TestO10
	    (R: in out RofA2; I: in IT2; A: in Arr1T)
     with Depends => (R =>+ (A, I)),
          Post    => R = R'Old'Update (S2 => R'Old.S2'Update (I => A, 55-I => R'Old.S2(55-I)'Update (1 => 0)));

  -----------------------------------------------
  -- [P] Record(1) of array(3)
  -----------------------------------------------
  procedure TestP01
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J, K)),
          Post    => (for all M in IT3 => (for all N in IT2 => (for all O in IT1 => (R.T3(M)(N)(O) in ET1)))) and R.S3 in Enum1TB and R.U3 in Boolean;

  procedure TestP02
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J, K)),
          Post    => (for all M in IT3 => (for all N in IT2 => (for all O in IT1 => (if (M /= I or N /= J or O /= K) then R.T3 (M) (N) (O) = R'Old.T3 (M) (N) (O))))) and R.T3 (I) (J) (K) = E and R.S3 = R'Old.S3 and R.U3 = R'Old.U3;

  procedure TestP03
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J, K)),
          Post    => R = R'Old'Update (T3 => R'Old.T3'Update (I => R'Old.T3(I)'Update (J => R'Old.T3(I)(J)'Update (K => E))));

  procedure TestP04
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J, K)),
          Post    => R.T3 = R'Old.T3'Update (I => R'Old.T3(I)'Update (J => R'Old.T3(I)(J)'Update (K => E))) and R.S3 = R'Old.S3 and R.U3 = R'Old.U3;

  procedure TestP05
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; A: in Arr3T;
	     B: in Arr2T; C: in Arr1T; D: in ET1)
     with Depends => (R =>+ (A, B, C, D, I, J, K)),
          Post    => (for all M in IT3 => (for all N in IT2 => (for all O in IT1 => (R.T3(M)(N)(O) in ET1)))) and R.S3 in Enum1TB and R.U3 in Boolean;

  procedure TestP06
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; A: in Arr3T;
	     B: in Arr2T; C: in Arr1T; D: in ET1)
     with Depends => (R =>+ (A, B, C, D, I, J, K)),
          Post    => (for all M in IT3 => (if M /= I then R.T3 (M) = A (M))) and (for all N in IT2 => (if N /= J then R.T3 (I) (N) = B (N))) and (for all O in IT1 => (if O /= K then R.T3 (I) (J) (O) = C (O))) and R.T3 (I) (J) (K) = D and R.S3 = R'Old.S3 and not R.U3;

  procedure TestP07
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; A: in Arr3T;
	     B: in Arr2T; C: in Arr1T; D: in ET1)
     with Depends => (R =>+ (A, B, C, D, I, J, K)),
          Post    => R = R'Old'Update (T3 => A'Update (I => B'Update (J => C'Update (K => D))), U3 => false);

  procedure TestP08
	    (R: in out RofA3; I: in IT3; J: in IT2; K: in IT1; A: in Arr3T;
	     B: in Arr2T; C: in Arr1T; D: in ET1)
     with Depends => (R =>+ (A, B, C, D, I, J, K)),
          Post    => R.S3 = R'Old.S3 and R.T3 = A'Update (I => B'Update (J => C'Update (K => D))) and not R.U3;

  -----------------------------------------------
  -- [Q] Record(1) of array(mixed)
  -----------------------------------------------
  procedure TestQ01
	    (R: in out RofA4; I: in IT2; J: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I, J)),
          Post    => (for all N in IT1 => ((for all M in IT2 => (R.T4(M)(N) in ET1)) and R.S4(N) in ET1));

  procedure TestQ02
	    (R: in out RofA4; I: in IT2; J: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I, J)),
          Post    => (for all M in IT1 => (if M /= J then (R.S4 (M) = R'Old.S4 (M) and R.T4 (I) (M) = R'Old.T4 (I) (M)))) and (for all N in IT2 => (if N /= I then R.T4 (N) = R'Old.T4 (N))) and R.T4 (I) (J) = F and R.S4 (J) = E;

  procedure TestQ03
	    (R: in out RofA4; I: in IT2; J: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I, J)),
          Post    => R = R'Old'Update (S4 => R'Old.S4'Update (J => E), T4 => R'Old.T4'Update (I => R'Old.T4(I)'Update (J => F)));

  procedure TestQ04
	    (R: in out RofA4; I: in IT2; J: in IT1; E, F: in ET1)
     with Depends => (R =>+ (E, F, I, J)),
          Post    => R.S4 = R'Old.S4'Update (J => E) and R.T4 = R'Old.T4'Update (I => R'Old.T4(I)'Update (J => F));

  -----------------------------------------------
  -- [R] Array of record of array(1)
  -----------------------------------------------
  procedure TestR01
	    (A: in out AofRofA1; I: in IT3; J: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => (for all M in IT3 => (A(M) in RofA1 and A(M).T1 in Enum2T)) and (for all M in IT3 => (for all N in IT1 => (A(M).S1(N) in ET1)));

  procedure TestR02
	    (A: in out AofRofA1; I: in IT3; J: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => (for all M in IT3 => (if M /= I then A (M) = A'Old (M))) and (for all N in IT1 => (if N /= J then A (I) .S1 (N) = A'Old (I) .S1 (N))) and A (I) .T1 = A'Old (I) .T1 and A (I) .S1 (J) = E;

  procedure TestR03
	    (A: in out AofRofA1; I: in IT3; J: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => A = A'Old'Update (I => A'Old(I)'Update (S1 => A'Old(I).S1'Update (J => E)));

  procedure TestR04
	    (A: in out AofRofA1; I: in IT3; J: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => A = A'Old'Update (I => RofA1'(S1 => A'Old(I).S1'Update (J => E), T1 => A'Old(I).T1));

  procedure TestR05
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
     with Depends => (A =>+ (E, I, J, R, X)),
          Post    => (for all M in IT3 => (A(M) in RofA1 and A(M).T1 in Enum2T)) and (for all M in IT3 => (for all N in IT1 => (A(M).S1(N) in ET1)));

  procedure TestR06
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
     with Depends => (A =>+ (E, I, J, R, X)),
          Pre     => I /= X,
          Post    => (for all M in IT3 => (if (M /= I and M /= X) then A (M) = A'Old (M))) and (for all N in IT1 => (if N /= J then A (I) .S1 (N) = A'Old (I) .S1 (N))) and A (X) = R and A (I) .T1 = A'Old (I) .T1 and A (I) .S1 (J) = E and A (X) .T1 = R.T1 and A (X) .S1 = R.S1 and A (X) .S1 (J) = R.S1 (J);

  procedure TestR07
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
     with Depends => (A =>+ (E, I, J, R, X)),
          Pre     => I /= X,
          Post    => A = A'Old'Update (I => A'Old(I)'Update (S1 => A'Old(I).S1'Update (J => E)), X => R);

  procedure TestR08
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
     with Depends => (A =>+ (E, I, J, R, X)),
          Pre     => I /= X,
          Post    => A = A'Old'Update (I => RofA1'(S1 => A'Old(I).S1'Update (J => E), T1 => A'Old(I).T1), X => R);

  procedure TestR09
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
     with Depends => (A =>+ (E, I, J, R, X)),
          Pre     => I /= X,
          Post    => A = A'Old'Update (X => R, I => A'Old(I)'Update (S1 => A'Old(I).S1'Update (J => E)));

  procedure TestR10
	    (A: in out AofRofA1; I, X: in IT3; J: in IT1; E: in ET1; R: in RofA1)
     with Depends => (A =>+ (E, I, J, R, X)),
          Pre     => I /= X,
          Post    => A = A'Old'Update (X => R, I => RofA1'(S1 => A'Old(I).S1'Update (J => E), T1 => A'Old(I).T1));

  procedure TestR11
	    (A: out AofRofA1; I: in IT3; J: in IT1; B: in AofRofA1; C: RofA1; D: Arr1T;
	     E: in ET1)
     with Depends => (A => (B, C, D, E, I, J)),
          Post    => (for all M in IT3 => (A(M) in RofA1 and A(M).T1 in Enum2T)) and (for all M in IT3 => (for all N in IT1 => (A(M).S1(N) in ET1)));

  procedure TestR12
	    (A: out AofRofA1; I: in IT3; J: in IT1; B: in AofRofA1; C: RofA1; D: Arr1T;
	     E: in ET1)
     with Depends => (A => (B, C, D, E, I, J)),
          Post    => (for all M in IT3 => (if M /= I then A (M) = B (M))) and (for all N in IT1 => (if N /= J then A (I) .S1 (N) = D (N))) and A (I) .T1 = C.T1 and A (I) .S1 (J) = E;

  procedure TestR13
	    (A: out AofRofA1; I: in IT3; J: in IT1; B: in AofRofA1; C: RofA1; D: Arr1T;
	     E: in ET1)
     with Depends => (A => (B, C, D, E, I, J)),
          Post    => A = B'Update (I => C'Update (S1 => D'Update (J => E)));

  procedure TestR14
	    (A: out AofRofA1; I: in IT3; J: in IT1; B: in AofRofA1; C: RofA1; D: Arr1T;
	     E: in ET1)
     with Depends => (A => (B, C, D, E, I, J)),
          Post    => A = B'Update (I => RofA1'(S1 => D'Update (J => E), T1 => C.T1));

  -----------------------------------------------
  -- [S] Array of record of array(mixed)
  -----------------------------------------------
  procedure TestS01
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => (for all M in IT4 => (A(M) in RofA4)) and (for all M in IT4 => (for all N in IT1 => (A(M).S4(N) in ET1))) and (for all M in IT4 => (for all N in IT2 => (for all O in IT1 => (A(M).T4(N)(O) in ET1))));

  procedure TestS02
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => (for all M in IT4 => (if M /= I then A (M) = A'Old (M))) and (for all N in IT2 => (if N /= J then A (I) .T4 (N) = A'Old (I) .T4 (N))) and (for all O in IT1 => (if O /= K then A (I) .T4 (J) (O) = A'Old (I) .T4 (J) (O))) and A (I) .S4 = A'Old (I) .S4 and A (I) .T4 (J) (K) = E;

  procedure TestS03
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => A = A'Old'Update (I => A'Old(I)'Update (T4 => A'Old(I).T4'Update (J => A'Old(I).T4(J)'Update (K => E))));

  procedure TestS04
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J, K)),
          Post    => A = A'Old'Update (I => RofA4'(S4 => A'Old(I).S4,  T4 => A'Old(I).T4'Update (J => A'Old(I).T4(J)'Update (K => E))));

  procedure TestS05
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E, F: in ET1)
     with Depends => (A =>+ (E, F, I, J, K)),
          Post    => (for all M in IT4 => (A(M) in RofA4)) and (for all M in IT4 => (for all N in IT1 => (A(M).S4(N) in ET1))) and (for all M in IT4 => (for all N in IT2 => (for all O in IT1 => (A(M).T4(N)(O) in ET1))));

  procedure TestS06
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E, F: in ET1)
     with Depends => (A =>+ (E, F, I, J, K)),
          Post    => (for all M in IT4 => (if M /= I then A (M) = A'Old (M))) and (for all N in IT2 => (if N /= J then A (I) .T4 (N) = A'Old (I) .T4 (N))) and (for all O in IT1 => (if O /= K then (A (I) .T4 (J) (O) = A'Old (I) .T4 (J) (O) and A (I) .S4 (O) = A'Old (I) .S4 (O)))) and A (I) .T4 (J) (K) = E and A (I) .S4 (K) = F;

  procedure TestS07
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E, F: in ET1)
     with Depends => (A =>+ (E, F, I, J, K)),
          Post    => A = A'Old'Update (I => A'Old(I)'Update (T4 => A'Old(I).T4'Update (J => A'Old(I).T4(J)'Update (K => E)), S4 => A'Old(I).S4'Update (K => F)));

  procedure TestS08
	    (A: in out AofRofA2; I: in IT4; J: in IT2; K: in IT1; E, F: in ET1)
     with Depends => (A =>+ (E, F, I, J, K)),
          Post    => A = A'Old'Update (I => RofA4'(S4 => A'Old(I).S4'Update (K => F),  T4 => A'Old(I).T4'Update (J => A'Old(I).T4(J)'Update (K => E))));

  -----------------------------------------------
  -- [T] Record of array of record(1)
  -----------------------------------------------
  procedure TestT01
	    (R: in out RofAofR1; I: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => (for all N in IT1 => (R.A1(N) in Rec1T and R.A1(N).F1 in ET1 and R.A1(N).G1 in ET2)) and R.B1 in Boolean and R.C1 in Enum1T;

  procedure TestT02
	    (R: in out RofAofR1; I: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => (for all N in IT1 => (if N /= I then R.A1 (N) = R'Old.A1 (N))) and R.A1 (I) .F1 = E and R.A1 (I) .G1 = R'Old.A1 (I) .G1 and R.B1 = R'Old.B1 and R.C1 = R'Old.C1;

  procedure TestT03
	    (R: in out RofAofR1; I: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => R = R'Old'Update (A1 => R'Old.A1'Update (I => R'Old.A1(I)'Update (F1 => E)));

  procedure TestT04
	    (R: in out RofAofR1; I: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => R = RofAofR1'(A1 => R'Old.A1'Update (I => Rec1T'(F1 => E, G1 => R'Old.A1(I).G1)),  B1 => R'Old.B1,  C1 => R'Old.C1);

  procedure TestT05
	    (R: in out RofAofR1; I: in IT1; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F, I)),
          Post    => (for all N in IT1 => (R.A1(N) in Rec1T and R.A1(N).F1 in ET1 and R.A1(N).G1 in ET2)) and R.B1 in Boolean and R.C1 in Enum1T;

  procedure TestT06
	    (R: in out RofAofR1; I: in IT1; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F, I)),
          Post    => (for all N in IT1 => (if N /= I then R.A1 (N) = R'Old.A1 (N))) and R.A1 (I) .F1 = E and R.A1 (I) .G1 = F and R.B1 and R.C1 = R'Old.C1;

  procedure TestT07
	    (R: in out RofAofR1; I: in IT1; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F, I)),
          Post    => R = R'Old'Update (A1 => R'Old.A1'Update (I => R'Old.A1(I)'Update (F1 => E, G1 => F)), B1 => true);

  procedure TestT08
	    (R: in out RofAofR1; I: in IT1; E: in ET1; F: in ET2)
     with Depends => (R =>+ (E, F, I)),
          Post    => R = RofAofR1'(A1 => R'Old.A1'Update (I => Rec1T'(F1 => E, G1 => F)),  B1 => true,  C1 => R'Old.C1);

  -----------------------------------------------
  -- [U] Record of array of record(mixed)
  -----------------------------------------------
  procedure TestU01
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => (for all N in IT4 => (R.B2(N) in Rec5T and R.B2(N).F5 in Rec2T and R.B2(N).F5.F2 in ET3 and R.B2(N).F5.G2 in Rec1T and R.B2(N).F5.G2.F1 in ET1 and R.B2(N).F5.G2.G1 in ET2 and R.B2(N).F5.H2 in Enum1TA and R.B2(N).G5 in Boolean and R.B2(N).H5 in Rec1T and R.B2(N).H5.F1 in ET1 and R.B2(N).H5.G1 in ET2)) and R.A2 in IT4;

  procedure TestU02
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => (for all N in IT4 => (if N /= I then R.B2 (N) = R'Old.B2 (N))) and R.B2 (I) .F5.G2.F1 = E and R.B2 (I) .F5.G2.G1 = R'Old.B2 (I) .F5.G2.G1 and R.B2 (I) .F5.F2 = R'Old.B2 (I) .F5.F2 and R.B2 (I) .F5.H2 = R'Old.B2 (I) .F5.H2 and R.B2 (I) .G5 = R'Old.B2 (I) .G5 and R.B2 (I) .H5 = R'Old.B2 (I) .H5 and R.B2 (I) .H5.F1 = R'Old.B2 (I) .H5.F1 and R.B2 (I) .H5.G1 = R'Old.B2 (I) .H5.G1 and R.A2 = R'Old.A2;

  procedure TestU03
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => R = R'Old'Update (B2 => R'Old.B2'Update (I => R'Old.B2(I)'Update (F5 => R'Old.B2(I).F5'Update (G2 => R'Old.B2(I).F5.G2 'Update (F1 => E)))));

  procedure TestU04
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => R = RofAofR2'(A2 => R'Old.A2,  B2 => R'Old.B2'Update (I => Rec5T'(F5 => Rec2T'(F2 => R'Old.B2(I).F5.F2,  G2 => Rec1T'(F1 => E,  G1 => R'Old.B2(I).F5.G2.G1),  H2 => R'Old.B2(I).F5.H2),  G5 => R'Old.B2(I).G5,  H5 => Rec1T'(F1 => R'Old.B2(I).H5.F1,  G1 => R'Old.B2(I).H5.G1))));

  procedure TestU05
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Post    => (for all N in IT4 => (R.B2(N) in Rec5T and R.B2(N).F5 in Rec2T and R.B2(N).F5.F2 in ET3 and R.B2(N).F5.G2 in Rec1T and R.B2(N).F5.G2.F1 in ET1 and R.B2(N).F5.G2.G1 in ET2 and R.B2(N).F5.H2 in Enum1TA and R.B2(N).G5 in Boolean and R.B2(N).H5 in Rec1T and R.B2(N).H5.F1 in ET1 and R.B2(N).H5.G1 in ET2)) and R.A2 in IT4;

  procedure TestU06
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Pre     => R.A2 /= I,
          Post    => (for all N in IT4 => (if (N /= I and N /= R'Old.A2) then R.B2 (N) = R'Old.B2 (N))) and R.B2 (I) .F5.G2.F1 = E and R.B2 (I) .F5.G2.G1 = R'Old.B2 (I) .F5.G2.G1 and R.B2 (I) .F5.F2 = R'Old.B2 (I) .F5.F2 and R.B2 (I) .F5.H2 = R'Old.B2 (I) .F5.H2 and R.B2 (I) .G5 = R'Old.B2 (I) .G5 and R.B2 (I) .H5 = R'Old.B2 (I) .H5 and R.B2 (I) .H5.F1 = R'Old.B2 (I) .H5.F1 and R.B2 (I) .H5.G1 = R'Old.B2 (I) .H5.G1 and R.B2 (R'Old.A2) .F5.G2.F1 = E and R.B2 (R'Old.A2) .F5.G2.G1 = R'Old.B2 (R'Old.A2) .F5.G2.G1 and R.B2 (R'Old.A2) .F5.F2 = R'Old.B2 (R'Old.A2) .F5.F2 and R.B2 (R'Old.A2) .F5.H2 = R'Old.B2 (R'Old.A2) .F5.H2 and R.B2 (R'Old.A2) .G5 = R'Old.B2 (R'Old.A2) .G5 and R.B2 (R'Old.A2) .H5 = R'Old.B2 (R'Old.A2) .H5 and R.B2 (R'Old.A2) .H5.F1 = R'Old.B2 (R'Old.A2) .H5.F1 and R.B2 (R'Old.A2) .H5.G1 = R'Old.B2 (R'Old.A2) .H5.G1 and R.A2 = I;

  procedure TestU07
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Pre     => R.A2 /= I,
          Post    => R = R'Old'Update (A2 => I, B2 => R'Old.B2'Update (I     => R'Old.B2(I)'Update (F5 => R'Old.B2(I).F5'Update (G2 => R'Old.B2(I).F5.G2'Update (F1 => E))), R'Old.A2 => R'Old.B2(R'Old.A2)'Update (F5 => R'Old.B2(R'Old.A2).F5'Update (G2 => R'Old.B2(R'Old.A2).F5.G2'Update (F1 => E)))));

  procedure TestU08
	    (R: in out RofAofR2; I: in IT4; E: in ET1)
     with Depends => (R =>+ (E, I)),
          Pre     => R.A2 /= I,
          Post    => R = RofAofR2'(A2 => I,  B2 => R'Old.B2'Update (I     => Rec5T'(F5 => Rec2T'(F2 => R'Old.B2(I).F5.F2,  G2 => Rec1T'(F1 => E,  G1 => R'Old.B2(I).F5.G2.G1),  H2 => R'Old.B2(I).F5.H2),  G5 => R'Old.B2(I).G5,  H5 => Rec1T'(F1 => R'Old.B2(I).H5.F1,  G1 => R'Old.B2(I).H5.G1)), R'Old.A2 => Rec5T'(F5 => Rec2T'(F2 => R'Old.B2(R'Old.A2).F5.F2,  G2 => Rec1T'(F1 => E,  G1 => R'Old.B2(R'Old.A2).F5.G2.G1),  H2 => R'Old.B2(R'Old.A2).F5.H2),  G5 => R'Old.B2(R'Old.A2).G5,  H5 => Rec1T'(F1 => R'Old.B2(R'Old.A2).H5.F1,  G1 => R'Old.B2(R'Old.A2).H5.G1))));

  -----------------------------------------------
  -- [V] Array of record of array of record
  -----------------------------------------------
  procedure TestV01
	    (A: in out AofRofAofR; I: in IT2; J: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => (for all M in IT2 => (A(M) in RofAofR1 and (for all N in IT1 => (A(M).A1(N) in Rec1T and A(M).A1(N).F1 in ET1 and A(M).A1(N).G1 in ET2)) and A(M).B1 in Boolean and A(M).C1 in Enum1T));

  procedure TestV02
	    (A: in out AofRofAofR; I: in IT2; J: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => (for all M in IT2 => (if M /= I then A (M) = A'Old (M))) and (for all N in IT1 => (if N /= J then A (I) .A1 (N) = A'Old (I) .A1 (N))) and A (I) .A1 (J) .F1 = E and A (I) .A1 (J) .G1 = A'Old (I) .A1 (J) .G1 and A (I) .B1 = A'Old (I) .B1 and A (I) .C1 = A'Old (I) .C1;

  procedure TestV03
	    (A: in out AofRofAofR; I: in IT2; J: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => A = A'Old'Update (I => A'Old(I)'Update (A1 => A'Old(I).A1'Update (J => A'Old(I).A1(J)'Update (F1 => E))));

 procedure TestV04
	    (A: in out AofRofAofR; I: in IT2; J: in IT1; E: in ET1)
     with Depends => (A =>+ (E, I, J)),
          Post    => A(I) = RofAofR1'(A1 => A'Old(I).A1'Update (J => Rec1T'(F1 => E, G1 => A'Old(I).A1(J).G1)),  B1 => A'Old(I).B1,  C1 => A'Old(I).C1);

  -----------------------------------------------
  -- [W] Record of array of record of array
  -----------------------------------------------
  procedure TestW01
	    (R: in out RofAofRofA; I: in IT3; J: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J)),
          Post    => (for all M in IT3 => (R.D1(M) in RofA1 and R.D1(M).T1 in Enum2T and (for all N in IT1 => (R.D1(M).S1(N) in ET1)))) and (for all N in IT1 => (R.E1(N) in ET1));

  procedure TestW02
	    (R: in out RofAofRofA; I: in IT3; J: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J)),
          Post    => (for all M in IT3 => (if M /= I then R.D1 (M) = R'Old.D1 (M))) and (for all N in IT1 => (if N /= J then R.D1 (I) .S1 (N) = R'Old.D1 (I) .S1 (N))) and R.E1 = R'Old.E1;

  procedure TestW03
	    (R: in out RofAofRofA; I: in IT3; J: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J)),
          Post    => R = R'Old'Update (D1 => R'Old.D1'Update (I => R'Old.D1(I)'Update (S1 => R'Old.D1(I).S1'Update (J => E))));

  procedure TestW04
	    (R: in out RofAofRofA; I: in IT3; J: in IT1; E: in ET1)
     with Depends => (R =>+ (E, I, J)),
          Post    => R = RofAofRofA'(D1 => R'Old.D1'Update (I => RofA1'(S1 => R'Old.D1(I).S1'Update (J => E),  T1 => R'Old.D1(I).T1)),  E1 => R'Old.E1);

end AR;
