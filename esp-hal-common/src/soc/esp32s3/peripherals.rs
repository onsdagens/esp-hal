use esp32s3 as pac;
// We need to export this for users to use
pub use pac::Interrupt;

// We need to export this in the hal for the drivers to use
pub(crate) use self::peripherals::*;

crate::peripherals! {
    AES => true,
    APB_CTRL => true,
    APB_SARADC => true,
    DEBUG_ASSIST => true,
    DMA => true,
    DS => true,
    EFUSE => true,
    EXTMEM => true,
    GPIO => true,
    GPIOSD => true,
    HMAC => true,
    I2C0 => true,
    I2C1 => true,
    I2S0 => true,
    I2S1 => true,
    INTERRUPT_CORE0 => true,
    INTERRUPT_CORE1 => true,
    IO_MUX => true,
    LCD_CAM => true,
    LEDC => true,
    PCNT => true,
    PERI_BACKUP => true,
    PWM0 => true,
    PWM1 => true,
    RMT => true,
    RNG => true,
    RSA => true,
    RTC_CNTL => true,
    RTC_I2C => true,
    RTCIO => true,
    SENS => true,
    SENSITIVE => true,
    SHA => true,
    SPI0 => true,
    SPI1 => true,
    SPI2 => true,
    SPI3 => true,
    SYSTEM => true,
    SYSTIMER => true,
    TIMG0 => true,
    TIMG1 => true,
    TWAI => true,
    UART0 => true,
    UART1 => true,
    UART2 => true,
    UHCI0 => true,
    UHCI1 => true,
    USB0 => true,
    USB_DEVICE => true,
    USB_WRAP => true,
    WCL => true,
    XTS_AES => true,
    RADIO => false
}
