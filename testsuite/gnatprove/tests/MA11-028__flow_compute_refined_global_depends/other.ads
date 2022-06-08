package Other
  with Abstract_State => Other_State,
       Initializes    => Other_State
is
   function Wibble return Boolean
     with Global   => Other_State,
          Annotate => (GNATprove, Always_Return);
end Other;
