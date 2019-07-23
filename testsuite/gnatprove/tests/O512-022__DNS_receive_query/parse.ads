with Types; use Types;
with Interfaces; use Interfaces;

package Parse is pragma SPARK_Mode (On);

   type Parse_Result_T (Return_Code : Return_Code_T := Invalid_Query) is record
      case Return_Code is
         when OK =>
            Header : Query_Header;
         when Invalid_Query =>
            null;
      end case;
   end record;

   procedure Parse_Header(Query : Network_DNS_Query;
                          Result : out Parse_Result_T)
                          with Pre => not Result'Constrained;
   -- The functional behaviour is not specified in the Post. Would be cumbersome
   -- to do. Would it bring additional assurance?
end;
