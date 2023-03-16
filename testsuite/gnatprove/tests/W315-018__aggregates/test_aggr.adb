
procedure Test_Aggr with Spark_Mode is

   subtype COMPONENT is INTEGER;

   MAX_LEN : constant := 10;

   subtype LENGTH is NATURAL range 0 .. MAX_LEN;

   type PARENT (B : BOOLEAN := TRUE; L : LENGTH := 1) is
      record
         I : INTEGER;
         case B is
            when TRUE =>
               S : STRING (1 .. L);
               C : COMPONENT;
            when FALSE =>
               F : FLOAT := 5.0;
         end case;
      end record;

   function CREATE ( B : BOOLEAN;
                     L : LENGTH;
                     I : INTEGER;
                     S : STRING;
                     C : COMPONENT;
                     F : FLOAT
                    ) return PARENT
     with Global => null;

   function CREATE
     ( B : BOOLEAN;
       L : LENGTH;
       I : INTEGER;
       S : STRING;
       C : COMPONENT;
       F : FLOAT
      ) return PARENT
   is
   begin
      case B is
         when TRUE =>
            return (TRUE, L, I, S, C);
         when FALSE =>
            return (FALSE, L, I, F);
      end case;
   end CREATE;

begin
   null;
end Test_Aggr;
