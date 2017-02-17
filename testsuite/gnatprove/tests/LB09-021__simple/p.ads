package P is

  type Enum is (A, B);

  type S (D : Enum) is record
    case D is
        when A =>
          Bool_Field : Boolean;
        when B =>
          Int_Field : Integer;
    end case;
  end record;

  type T (Z : Enum) is record
    Field : S (Z);
  end record;

  procedure P (V : in out T);
end;
