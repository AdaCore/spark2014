-- Test package for adjusting strings to a fixed length
pragma SPARK_Mode;

package body Fixed_String is

    --------------------------------------------------------------------
    -- Trim_String
    -- Trim or pad one string to the length of another.
    procedure Trim_String( Change :    out String;
                           New_Val: in     String )
    is
        Len : Natural := Natural'Min( Change'Length, New_Val'Length );

    begin
        Change := (others => Character'First);

        Change(Change'First..Change'First+Integer(Len-1)) :=
          New_Val(New_Val'First..New_Val'First+Integer(Len-1));
    end Trim_String;

    --------------------------------------------------------------------
    -- Create
    -- Return a new Object with the specified character width.
    function Create( Elem_Width: in Natural;
                     Name      : in String ) return Object
    is
        This: Object;

    begin
        This.Width := Elem_Width;

        -- assign name string
        Trim_String( Change => This.Name, New_Val => Name );

        return This;
    end Create;

    --------------------------------------------------------------------
    -- Elements
    -- Return string character width.
    function Elements( This: in Object ) return Natural
    is ( This.Width );

    --------------------------------------------------------------------
    -- Null_String
    -- Return an empty string of the correct length.
    function Null_String( This: in Object ) return String
    is
        Value: String(1..This.Width) := (others => Character'First);

    begin
        return Value;
    end Null_String;

    --------------------------------------------------------------------
    -- Convert
    -- Trim or pad provided string to the specified length.
    function Convert( This: in Object; In_String: in String )
                     return String
    is
        Len       : Natural := Natural'Min( In_String'Length,
                                            This.Width );
        Out_String: String  := This.Null_String;

    begin
        Out_String(Out_String'First..Out_String'First+Integer(Len-1)) :=
          In_String(In_String'First..In_String'First+Integer(Len-1));

        return Out_String;
    end Convert;

end Fixed_String;
