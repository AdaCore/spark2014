with Framebuffer_LTDC;
private with ILI9341;
private with STM32.GPIO;
private with STM32.Device;

package Framebuffer_ILI9341 is

   pragma Elaborate_Body;

   type Frame_Buffer is limited
     new Framebuffer_LTDC.Frame_Buffer with private;

private

   --  Chip select and Data/Command select for the LCD screen
   LCD_CSX : STM32.GPIO.GPIO_Point renames STM32.Device.PC2;

   type Frame_Buffer
   is limited new Framebuffer_LTDC.Frame_Buffer with record
      Device : ILI9341.ILI9341_Device (Chip_Select => LCD_CSX'Access);
   end record;

end Framebuffer_ILI9341;
