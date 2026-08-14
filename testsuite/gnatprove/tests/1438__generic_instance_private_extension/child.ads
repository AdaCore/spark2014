with Root;

package Child is

   type Appender is new Root.Lists.Named_Element with private;

   type Appender_Access is access all Appender;

private

   type Appender is new Root.Lists.Named_Element with null record;

end Child;
