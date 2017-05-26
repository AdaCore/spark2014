-- Test package for adjusting strings to a fixed length
pragma SPARK_Mode;

package Fixed_String is

    type Object is tagged private;

    --------------------------------------------------------------------
    -- Create
    -- Return a new Object with the specified character width.
    function Create( Elem_Width: in Natural;
                     Name      : in String ) return Object
      with Post => Create'Result.Elements = Elem_Width;

    --------------------------------------------------------------------
    -- Elements
    -- Return string character width.
    function Elements( This: in Object ) return Natural
      with Inline;

    --------------------------------------------------------------------
    -- Null_String
    -- Return an empty string of the correct length.
    function Null_String( This: in Object ) return String
      with Inline,
      Post => Null_String'Result'Length = This.Elements;

    --------------------------------------------------------------------
    -- Convert
    -- Trim or pad provided string to the specified length.
    function Convert( This: in Object; In_String: in String )
                     return String
      with Post => Convert'Result'Length = This.Elements;

private
    type Object is tagged
        record
            Width: Natural       := 0;
            Name : String(1..20) := (others => Character'First);
        end record;

    --------------------------------------------------------------------
    -- Trim_String
    -- Trim or pad one string to the length of another.
    procedure Trim_String( Change :    out String;
                           New_Val: in     String )
      with Inline,
      Post => (for all I in Change'Range =>
            ((New_Val'First < 0 or else
                 I-Change'First <= Integer'Last-New_Val'First) and then
                   I-Change'First+New_Val'First <= New_Val'Last and then
                     Change(I) = New_Val(I-Change'First+New_Val'First))
          or Change(I) = Character'First );

end Fixed_String;
