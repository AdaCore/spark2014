package AR is

  type NatByte is range 0..255;

  subtype IT1 is NatByte range  1..10;
  subtype ET1 is NatByte range  0..99;

  subtype IT2 is IT1 range 1..5;

  type Arr1T is array (IT1) of ET1;
  type ArrHej is array (IT2) of ET1;

  -- A couple of examples of 'Updates with mixed choices in contracts.
  -- See body for tests of checks of 'Update in subprogram bodies

  procedure Test1 (A: in out Arr1T; I, J: in IT1; E: in ET1)
    with Depends => (A =>+ (E, I, J)),
    Post    =>
    A = A'Old'Update (I - 1 | I .. J + 2 => E - 1, J + 1 => E + 1);

  procedure Test2 (A: in out Arr1T; I, J: in IT1; E: in ET1)
    with Depends => (A =>+ (E, I, J)),
         Post    =>
     A = A'Old'Update (I - 1 | I .. J + 2 => E - 1, J + 1 => E + 1);

end AR;
