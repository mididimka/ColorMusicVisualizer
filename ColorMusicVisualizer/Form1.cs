using System;
using System.Collections.Generic;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.Json;
using System.Windows.Forms;
using NAudio.Wave;
using NAudio.CoreAudioApi;

namespace ColorMusicVisualizer
{
    public partial class Form1 : Form
    {
        // Аудио параметры
        private WasapiLoopbackCapture wasapiCapture;
        private WasapiOut silencePlayer;
        private SilenceProvider silenceProvider;
        private float[] audioBuffer;
        private float[] fftData;
        private readonly int chunkSize = 2048;

        // Параметры прожекторов
        private const int NumSpotlights = 8;
        private float[] spotlightIntensities;
        private float[] smoothIntensities;
        private Color[] spotlightColors;
        private double[] spotlightAngles;

        // Частотные границы для каждого прожектора (в Гц)
        private int[] freqLowBoundsHz;
        private int[] freqHighBoundsHz;

        // Эффекты
        private List<Particle> particles;
        private Random random = new Random();

        // Графика
        private Bitmap mainBuffer;
        private Graphics mainGraphics;
        private bool isRunning = true;
        private float totalIntensity = 0;
        private DateTime lastSoundTime = DateTime.Now;
        private bool hasSound = false;
        private DateTime lastDataReceived = DateTime.Now;

        // FPS
        private int frameCount = 0;
        private DateTime lastFpsUpdate = DateTime.Now;
        private float currentFps = 0;

        // Информация об устройстве
        private string currentDeviceName = "Поиск устройства...";
        private bool isAudioInitialized = false;

        // Для анализа темпа
        private float[] volumeHistory = new float[43];
        private int volumeIndex = 0;
        private float beatThreshold = 0;
        private bool isBeat = false;

        // Координаты прожекторов
        private float[] spotX;
        private float[] spotY;
        private float spotSize;

        // Режимы отображения
        private enum LayoutMode
        {
            Circular,   // Кругом
            Grid2x4,    // 2 строки x 4 колонки
            Grid1x8,    // 1 строка x 8 колонок
            Grid4x2     // 4 строки x 2 колонки
        }

        private LayoutMode currentLayout = LayoutMode.Circular;
        private bool isRectangular = false;
        private float spotWidth;
        private float spotHeight;

        // Настройки чувствительности для каждого диапазона
        private float[] spotSensitivity;
        private float[] spotMinBrightness;

        // Общие настройки
        private float globalSensitivity = 3.0f;
        private float globalBrightnessBoost = 2.5f;

        // Константы частот
        private const int MinFreq = 20;
        private const int MaxFreq = 20000;

        // Элементы управления
        private Panel controlsPanel;
        private NumericUpDown globalSensitivityNud;
        private NumericUpDown globalBrightnessNud;
        private NumericUpDown[] sensitivityNud;
        private NumericUpDown[] minBrightnessNud;
        private NumericUpDown[] lowFreqNud;
        private NumericUpDown[] highFreqNud;
        private NumericUpDown[] colorPickerNud;
        private ProgressBar[] levelIndicators;
        private Label[] currentLevelLabels;
        private Button resetButton;
        private Button saveButton;
        private Button loadButton;
        private ComboBox layoutModeCombo;
        private CheckBox rectangularCheckBox;
        private TrackBar spotSizeSlider;
        private Label spotSizeLabel;
        private NumericUpDown spotSizeNud; // Добавляем числовой регулятор для размера
        private bool controlsVisible = true;
        private bool spectrumVisible = true;
        private bool infoVisible = true;

        // Путь к файлу сохранений
        private string settingsPath = "color_music_settings.json";

        // Класс для сохранения настроек
        [Serializable]
        public class Settings
        {
            public float GlobalSensitivity { get; set; }
            public float GlobalBrightnessBoost { get; set; }
            public int[] FreqLowBoundsHz { get; set; }
            public int[] FreqHighBoundsHz { get; set; }
            public float[] SpotSensitivity { get; set; }
            public float[] SpotMinBrightness { get; set; }
            public int[] SpotColorsArgb { get; set; }
            public bool SpectrumVisible { get; set; }
            public bool InfoVisible { get; set; }
            public int LayoutMode { get; set; }
            public bool IsRectangular { get; set; }
            public float SpotSize { get; set; }
            public DateTime SaveDate { get; set; }
        }

        public Form1()
        {
            InitializeComponent();
            SetupForm();

            InitializeArrays();
            CreateControls();
            InitializeSpotlights();

            particles = new List<Particle>();

            var timer = new Timer();
            timer.Interval = 33;
            timer.Tick += OnTimerTick;
            timer.Start();

            InitializeAudioLoopbackWithSilence();
            CreateMainBuffer();

            LoadSettings();
        }

        private void InitializeArrays()
        {
            audioBuffer = new float[chunkSize];
            fftData = new float[chunkSize / 2];
            spotlightIntensities = new float[NumSpotlights];
            smoothIntensities = new float[NumSpotlights];
            spotX = new float[NumSpotlights];
            spotY = new float[NumSpotlights];
            spotSensitivity = new float[NumSpotlights];
            spotMinBrightness = new float[NumSpotlights];
            freqLowBoundsHz = new int[NumSpotlights];
            freqHighBoundsHz = new int[NumSpotlights];
            spotlightColors = new Color[NumSpotlights];

            for (int i = 0; i < NumSpotlights; i++)
            {
                spotSensitivity[i] = 1.0f;
                spotMinBrightness[i] = 0.12f;

                double logMin = Math.Log10(MinFreq);
                double logMax = Math.Log10(MaxFreq);
                double logLow = logMin + (logMax - logMin) * i / NumSpotlights;
                double logHigh = logMin + (logMax - logMin) * (i + 1) / NumSpotlights;

                freqLowBoundsHz[i] = (int)Math.Pow(10, logLow);
                freqHighBoundsHz[i] = (int)Math.Pow(10, logHigh);

                double hue = (double)i / NumSpotlights;
                spotlightColors[i] = HSVToColor(hue, 1.0, 1.0);
            }
            freqHighBoundsHz[NumSpotlights - 1] = MaxFreq;

            spotSize = 120f;
            spotWidth = 100f;
            spotHeight = 80f;
        }

        private void SetupForm()
        {
            this.Text = "Цветомузыка - 8 прожекторов (настраиваемые)";
            this.Size = new Size(1600, 1000);
            this.StartPosition = FormStartPosition.CenterScreen;
            this.BackColor = Color.Black;
            this.DoubleBuffered = true;
            this.KeyPreview = true;
            this.KeyDown += Form1_KeyDown;
            this.Resize += Form1_Resize;
            this.FormClosing += Form1_FormClosing;
            this.Paint += Form1_Paint;
        }

        private void CreateControls()
        {
            controlsPanel = new Panel();
            controlsPanel.BackColor = Color.FromArgb(200, 0, 0, 0);
            controlsPanel.Location = new Point(5, 5);
            controlsPanel.Size = new Size(450, 700);
            controlsPanel.BorderStyle = BorderStyle.FixedSingle;
            controlsPanel.AutoScroll = true;

            int yOffset = 5;

            // Заголовок
            Label titleLabel = new Label();
            titleLabel.Text = "НАСТРОЙКИ ЦВЕТОМУЗЫКИ";
            titleLabel.ForeColor = Color.Lime;
            titleLabel.BackColor = Color.Transparent;
            titleLabel.Font = new Font("Segoe UI", 10, FontStyle.Bold);
            titleLabel.Location = new Point(5, yOffset);
            titleLabel.Size = new Size(420, 25);
            controlsPanel.Controls.Add(titleLabel);
            yOffset += 30;

            // Глобальные настройки
            Panel globalPanel = new Panel();
            globalPanel.BackColor = Color.FromArgb(40, 40, 40);
            globalPanel.Location = new Point(5, yOffset);
            globalPanel.Size = new Size(420, 35);
            controlsPanel.Controls.Add(globalPanel);

            Label globalSensTitle = new Label();
            globalSensTitle.Text = "Общая чувствительность:";
            globalSensTitle.ForeColor = Color.White;
            globalSensTitle.BackColor = Color.Transparent;
            globalSensTitle.Font = new Font("Segoe UI", 8);
            globalSensTitle.Location = new Point(5, 8);
            globalSensTitle.Size = new Size(130, 20);
            globalPanel.Controls.Add(globalSensTitle);

            globalSensitivityNud = new NumericUpDown();
            globalSensitivityNud.Minimum = 0.5m;
            globalSensitivityNud.Maximum = 8.0m;
            globalSensitivityNud.DecimalPlaces = 1;
            globalSensitivityNud.Increment = 0.1m;
            globalSensitivityNud.Value = 3.0m;
            globalSensitivityNud.Width = 60;
            globalSensitivityNud.Height = 22;
            globalSensitivityNud.Location = new Point(140, 6);
            globalSensitivityNud.BackColor = Color.FromArgb(40, 40, 40);
            globalSensitivityNud.ForeColor = Color.Lime;
            globalSensitivityNud.ValueChanged += GlobalSensitivityNud_ValueChanged;
            globalPanel.Controls.Add(globalSensitivityNud);

            Label globalBrightTitle = new Label();
            globalBrightTitle.Text = "Усиление яркости:";
            globalBrightTitle.ForeColor = Color.White;
            globalBrightTitle.BackColor = Color.Transparent;
            globalBrightTitle.Font = new Font("Segoe UI", 8);
            globalBrightTitle.Location = new Point(220, 8);
            globalBrightTitle.Size = new Size(100, 20);
            globalPanel.Controls.Add(globalBrightTitle);

            globalBrightnessNud = new NumericUpDown();
            globalBrightnessNud.Minimum = 0.5m;
            globalBrightnessNud.Maximum = 5.0m;
            globalBrightnessNud.DecimalPlaces = 1;
            globalBrightnessNud.Increment = 0.1m;
            globalBrightnessNud.Value = 2.5m;
            globalBrightnessNud.Width = 60;
            globalBrightnessNud.Height = 22;
            globalBrightnessNud.Location = new Point(325, 6);
            globalBrightnessNud.BackColor = Color.FromArgb(40, 40, 40);
            globalBrightnessNud.ForeColor = Color.Lime;
            globalBrightnessNud.ValueChanged += GlobalBrightnessNud_ValueChanged;
            globalPanel.Controls.Add(globalBrightnessNud);

            yOffset += 40;

            // Настройки отображения
            Panel displayPanel = new Panel();
            displayPanel.BackColor = Color.FromArgb(40, 40, 40);
            displayPanel.Location = new Point(5, yOffset);
            displayPanel.Size = new Size(420, 80);
            controlsPanel.Controls.Add(displayPanel);

            int dy = 5;

            Label layoutTitle = new Label();
            layoutTitle.Text = "Расположение:";
            layoutTitle.ForeColor = Color.White;
            layoutTitle.BackColor = Color.Transparent;
            layoutTitle.Font = new Font("Segoe UI", 8);
            layoutTitle.Location = new Point(5, dy);
            layoutTitle.Size = new Size(80, 20);
            displayPanel.Controls.Add(layoutTitle);

            layoutModeCombo = new ComboBox();
            layoutModeCombo.Items.AddRange(new string[] { "Кругом", "2 строки x 4 колонки", "1 строка x 8 колонок", "4 строки x 2 колонки" });
            layoutModeCombo.SelectedIndex = 0;
            layoutModeCombo.Width = 150;
            layoutModeCombo.Height = 25;
            layoutModeCombo.Location = new Point(90, dy);
            layoutModeCombo.BackColor = Color.FromArgb(40, 40, 40);
            layoutModeCombo.ForeColor = Color.White;
            layoutModeCombo.DropDownStyle = ComboBoxStyle.DropDownList;
            layoutModeCombo.SelectedIndexChanged += LayoutModeCombo_SelectedIndexChanged;
            displayPanel.Controls.Add(layoutModeCombo);

            rectangularCheckBox = new CheckBox();
            rectangularCheckBox.Text = "Прямоугольные прожекторы";
            rectangularCheckBox.ForeColor = Color.White;
            rectangularCheckBox.BackColor = Color.Transparent;
            rectangularCheckBox.Location = new Point(260, dy);
            rectangularCheckBox.Size = new Size(150, 22);
            rectangularCheckBox.CheckedChanged += RectangularCheckBox_CheckedChanged;
            displayPanel.Controls.Add(rectangularCheckBox);
            dy += 28;

            Label sizeTitle = new Label();
            sizeTitle.Text = "Размер прожекторов:";
            sizeTitle.ForeColor = Color.White;
            sizeTitle.BackColor = Color.Transparent;
            sizeTitle.Font = new Font("Segoe UI", 8);
            sizeTitle.Location = new Point(5, dy);
            sizeTitle.Size = new Size(120, 20);
            displayPanel.Controls.Add(sizeTitle);

            spotSizeSlider = new TrackBar();
            spotSizeSlider.Minimum = 50;
            spotSizeSlider.Maximum = 1500; // Увеличено до 1500
            spotSizeSlider.Value = 120;
            spotSizeSlider.TickFrequency = 50;
            spotSizeSlider.Width = 150;
            spotSizeSlider.Height = 30;
            spotSizeSlider.Location = new Point(130, dy - 5);
            spotSizeSlider.Scroll += SpotSizeSlider_Scroll;
            displayPanel.Controls.Add(spotSizeSlider);

            spotSizeNud = new NumericUpDown();
            spotSizeNud.Minimum = 50;
            spotSizeNud.Maximum = 1500;
            spotSizeNud.Value = 120;
            spotSizeNud.Width = 60;
            spotSizeNud.Height = 22;
            spotSizeNud.Location = new Point(290, dy);
            spotSizeNud.BackColor = Color.FromArgb(40, 40, 40);
            spotSizeNud.ForeColor = Color.Lime;
            spotSizeNud.ValueChanged += SpotSizeNud_ValueChanged;
            displayPanel.Controls.Add(spotSizeNud);

            spotSizeLabel = new Label();
            spotSizeLabel.Text = "px";
            spotSizeLabel.ForeColor = Color.Lime;
            spotSizeLabel.BackColor = Color.Transparent;
            spotSizeLabel.Font = new Font("Segoe UI", 8, FontStyle.Bold);
            spotSizeLabel.Location = new Point(355, dy);
            spotSizeLabel.Size = new Size(30, 20);
            displayPanel.Controls.Add(spotSizeLabel);

            yOffset += 85;

            // Кнопки сохранения/загрузки
            Panel buttonPanel = new Panel();
            buttonPanel.BackColor = Color.Transparent;
            buttonPanel.Location = new Point(5, yOffset);
            buttonPanel.Size = new Size(420, 35);

            saveButton = new Button();
            saveButton.Text = "💾 СОХРАНИТЬ";
            saveButton.BackColor = Color.FromArgb(60, 80, 60);
            saveButton.ForeColor = Color.White;
            saveButton.FlatStyle = FlatStyle.Flat;
            saveButton.Font = new Font("Segoe UI", 8, FontStyle.Bold);
            saveButton.Size = new Size(200, 30);
            saveButton.Location = new Point(0, 0);
            saveButton.Click += SaveButton_Click;
            buttonPanel.Controls.Add(saveButton);

            loadButton = new Button();
            loadButton.Text = "📂 ЗАГРУЗИТЬ";
            loadButton.BackColor = Color.FromArgb(60, 60, 80);
            loadButton.ForeColor = Color.White;
            loadButton.FlatStyle = FlatStyle.Flat;
            loadButton.Font = new Font("Segoe UI", 8, FontStyle.Bold);
            loadButton.Size = new Size(200, 30);
            loadButton.Location = new Point(210, 0);
            loadButton.Click += LoadButton_Click;
            buttonPanel.Controls.Add(loadButton);

            controlsPanel.Controls.Add(buttonPanel);
            yOffset += 40;

            // Разделитель
            Label separator = new Label();
            separator.Text = "─────────────────────────────────────────────────────────";
            separator.ForeColor = Color.Gray;
            separator.BackColor = Color.Transparent;
            separator.Font = new Font("Segoe UI", 6);
            separator.Location = new Point(5, yOffset);
            separator.Size = new Size(420, 15);
            controlsPanel.Controls.Add(separator);
            yOffset += 20;

            // Заголовок
            Label individualTitle = new Label();
            individualTitle.Text = "ИНДИВИДУАЛЬНЫЕ НАСТРОЙКИ ПРОЖЕКТОРОВ";
            individualTitle.ForeColor = Color.Cyan;
            individualTitle.BackColor = Color.Transparent;
            individualTitle.Font = new Font("Segoe UI", 8, FontStyle.Bold);
            individualTitle.Location = new Point(5, yOffset);
            individualTitle.Size = new Size(420, 20);
            controlsPanel.Controls.Add(individualTitle);
            yOffset += 25;

            sensitivityNud = new NumericUpDown[NumSpotlights];
            minBrightnessNud = new NumericUpDown[NumSpotlights];
            lowFreqNud = new NumericUpDown[NumSpotlights];
            highFreqNud = new NumericUpDown[NumSpotlights];
            colorPickerNud = new NumericUpDown[NumSpotlights];
            levelIndicators = new ProgressBar[NumSpotlights];
            currentLevelLabels = new Label[NumSpotlights];

            for (int i = 0; i < NumSpotlights; i++)
            {
                Color color = spotlightColors[i];

                // Рамка для прожектора
                Panel spotPanel = new Panel();
                spotPanel.BackColor = Color.FromArgb(60, 0, 0, 0);
                spotPanel.BorderStyle = BorderStyle.FixedSingle;
                spotPanel.Location = new Point(5, yOffset);
                spotPanel.Size = new Size(420, 85);
                spotPanel.Name = $"spotPanel_{i}";
                controlsPanel.Controls.Add(spotPanel);

                // Номер прожектора
                Label spotLabel = new Label();
                spotLabel.Text = $"Прожектор {i + 1}";
                spotLabel.ForeColor = color;
                spotLabel.BackColor = Color.Transparent;
                spotLabel.Font = new Font("Segoe UI", 8, FontStyle.Bold);
                spotLabel.Location = new Point(5, 5);
                spotLabel.Size = new Size(80, 20);
                spotPanel.Controls.Add(spotLabel);

                // Индикатор уровня сигнала
                ProgressBar levelBar = new ProgressBar();
                levelBar.Minimum = 0;
                levelBar.Maximum = 100;
                levelBar.Value = 0;
                levelBar.Width = 80;
                levelBar.Height = 15;
                levelBar.Location = new Point(90, 7);
                levelBar.ForeColor = color;
                spotPanel.Controls.Add(levelBar);
                levelIndicators[i] = levelBar;

                Label currentLevelLabel = new Label();
                currentLevelLabel.Text = "0%";
                currentLevelLabel.ForeColor = color;
                currentLevelLabel.BackColor = Color.Transparent;
                currentLevelLabel.Font = new Font("Segoe UI", 7, FontStyle.Bold);
                currentLevelLabel.Location = new Point(175, 5);
                currentLevelLabel.Size = new Size(40, 20);
                spotPanel.Controls.Add(currentLevelLabel);
                currentLevelLabels[i] = currentLevelLabel;

                // Выбор цвета
                Label colorLabel = new Label();
                colorLabel.Text = "Цвет:";
                colorLabel.ForeColor = Color.Gray;
                colorLabel.BackColor = Color.Transparent;
                colorLabel.Font = new Font("Segoe UI", 7);
                colorLabel.Location = new Point(230, 5);
                colorLabel.Size = new Size(35, 20);
                spotPanel.Controls.Add(colorLabel);

                NumericUpDown colorNud = new NumericUpDown();
                colorNud.Minimum = 0;
                colorNud.Maximum = 360;
                float hueValue = (float)GetHueFromColor(color);
                colorNud.Value = Math.Max(0, Math.Min(360, (decimal)hueValue));
                colorNud.Width = 60;
                colorNud.Height = 22;
                colorNud.Location = new Point(265, 3);
                colorNud.BackColor = Color.FromArgb(40, 40, 40);
                colorNud.ForeColor = color;
                colorNud.Tag = i;
                colorNud.ValueChanged += ColorNud_ValueChanged;
                spotPanel.Controls.Add(colorNud);
                colorPickerNud[i] = colorNud;

                Label degLabel = new Label();
                degLabel.Text = "°";
                degLabel.ForeColor = Color.Gray;
                degLabel.BackColor = Color.Transparent;
                degLabel.Font = new Font("Segoe UI", 7);
                degLabel.Location = new Point(328, 5);
                degLabel.Size = new Size(15, 20);
                spotPanel.Controls.Add(degLabel);

                // Частотный диапазон
                Label freqLabel = new Label();
                freqLabel.Text = "Частота:";
                freqLabel.ForeColor = Color.Gray;
                freqLabel.BackColor = Color.Transparent;
                freqLabel.Font = new Font("Segoe UI", 7);
                freqLabel.Location = new Point(5, 30);
                freqLabel.Size = new Size(45, 20);
                spotPanel.Controls.Add(freqLabel);

                NumericUpDown lowNud = new NumericUpDown();
                lowNud.Minimum = MinFreq;
                lowNud.Maximum = MaxFreq;
                int lowValue = Math.Max(MinFreq, Math.Min(MaxFreq, freqLowBoundsHz[i]));
                lowNud.Value = lowValue;
                lowNud.Width = 70;
                lowNud.Height = 22;
                lowNud.Location = new Point(55, 28);
                lowNud.BackColor = Color.FromArgb(40, 40, 40);
                lowNud.ForeColor = color;
                lowNud.Tag = i;
                lowNud.ValueChanged += LowFreqNud_ValueChanged;
                spotPanel.Controls.Add(lowNud);
                lowFreqNud[i] = lowNud;

                Label dashLabel = new Label();
                dashLabel.Text = "-";
                dashLabel.ForeColor = Color.Gray;
                dashLabel.BackColor = Color.Transparent;
                dashLabel.Font = new Font("Segoe UI", 8);
                dashLabel.Location = new Point(128, 30);
                dashLabel.Size = new Size(10, 20);
                spotPanel.Controls.Add(dashLabel);

                NumericUpDown highNud = new NumericUpDown();
                highNud.Minimum = MinFreq;
                highNud.Maximum = MaxFreq;
                int highValue = Math.Max(lowValue + 1, Math.Min(MaxFreq, freqHighBoundsHz[i]));
                highNud.Value = highValue;
                highNud.Width = 70;
                highNud.Height = 22;
                highNud.Location = new Point(140, 28);
                highNud.BackColor = Color.FromArgb(40, 40, 40);
                highNud.ForeColor = color;
                highNud.Tag = i;
                highNud.ValueChanged += HighFreqNud_ValueChanged;
                spotPanel.Controls.Add(highNud);
                highFreqNud[i] = highNud;

                freqLowBoundsHz[i] = lowValue;
                freqHighBoundsHz[i] = highValue;

                Label hzLabel = new Label();
                hzLabel.Text = "Гц";
                hzLabel.ForeColor = Color.Gray;
                hzLabel.BackColor = Color.Transparent;
                hzLabel.Font = new Font("Segoe UI", 7);
                hzLabel.Location = new Point(213, 30);
                hzLabel.Size = new Size(25, 20);
                spotPanel.Controls.Add(hzLabel);

                // Чувствительность
                Label sensText = new Label();
                sensText.Text = "Чувств:";
                sensText.ForeColor = Color.Gray;
                sensText.BackColor = Color.Transparent;
                sensText.Font = new Font("Segoe UI", 7);
                sensText.Location = new Point(250, 30);
                sensText.Size = new Size(45, 20);
                spotPanel.Controls.Add(sensText);

                NumericUpDown sensNud = new NumericUpDown();
                sensNud.Minimum = 0.1m;
                sensNud.Maximum = 5.0m;
                sensNud.DecimalPlaces = 1;
                sensNud.Increment = 0.1m;
                sensNud.Value = Math.Max(0.1m, Math.Min(5.0m, (decimal)spotSensitivity[i]));
                sensNud.Width = 50;
                sensNud.Height = 22;
                sensNud.Location = new Point(298, 28);
                sensNud.BackColor = Color.FromArgb(40, 40, 40);
                sensNud.ForeColor = color;
                sensNud.Tag = i;
                sensNud.ValueChanged += SensitivityNud_ValueChanged;
                spotPanel.Controls.Add(sensNud);
                sensitivityNud[i] = sensNud;

                // Минимальная яркость
                Label minText = new Label();
                minText.Text = "Мин. ярк:";
                minText.ForeColor = Color.Gray;
                minText.BackColor = Color.Transparent;
                minText.Font = new Font("Segoe UI", 7);
                minText.Location = new Point(5, 55);
                minText.Size = new Size(55, 20);
                spotPanel.Controls.Add(minText);

                NumericUpDown minNud = new NumericUpDown();
                minNud.Minimum = 0.05m;
                minNud.Maximum = 0.5m;
                minNud.DecimalPlaces = 2;
                minNud.Increment = 0.01m;
                minNud.Value = Math.Max(0.05m, Math.Min(0.5m, (decimal)spotMinBrightness[i]));
                minNud.Width = 50;
                minNud.Height = 22;
                minNud.Location = new Point(60, 53);
                minNud.BackColor = Color.FromArgb(40, 40, 40);
                minNud.ForeColor = color;
                minNud.Tag = i;
                minNud.ValueChanged += MinBrightnessNud_ValueChanged;
                spotPanel.Controls.Add(minNud);
                minBrightnessNud[i] = minNud;

                // Отображение текущего частотного диапазона
                Label rangeLabel = new Label();
                rangeLabel.Text = GetFreqRangeDisplay(i);
                rangeLabel.ForeColor = color;
                rangeLabel.BackColor = Color.Transparent;
                rangeLabel.Font = new Font("Segoe UI", 7, FontStyle.Bold);
                rangeLabel.Location = new Point(250, 55);
                rangeLabel.Size = new Size(160, 20);
                rangeLabel.Name = $"rangeLabel_{i}";
                spotPanel.Controls.Add(rangeLabel);

                yOffset += 90;
            }

            // Кнопка сброса
            resetButton = new Button();
            resetButton.Text = "СБРОСИТЬ ВСЕ НАСТРОЙКИ";
            resetButton.BackColor = Color.FromArgb(80, 80, 80);
            resetButton.ForeColor = Color.White;
            resetButton.FlatStyle = FlatStyle.Flat;
            resetButton.Font = new Font("Segoe UI", 8, FontStyle.Bold);
            resetButton.Location = new Point(5, yOffset + 5);
            resetButton.Size = new Size(420, 30);
            resetButton.Click += ResetButton_Click;
            controlsPanel.Controls.Add(resetButton);

            controlsPanel.Height = yOffset + 50;
            this.Controls.Add(controlsPanel);
        }

        private void SpotSizeNud_ValueChanged(object sender, EventArgs e)
        {
            if (spotSizeNud != null)
            {
                int newSize = (int)spotSizeNud.Value;
                spotSize = newSize;
                if (spotSizeSlider != null)
                    spotSizeSlider.Value = newSize;
                spotWidth = spotSize * 0.8f;
                spotHeight = spotSize * 0.6f;
                if (spotSizeLabel != null)
                    spotSizeLabel.Text = newSize.ToString();
            }
        }

        private double GetHueFromColor(Color color)
        {
            float r = color.R / 255f;
            float g = color.G / 255f;
            float b = color.B / 255f;

            float max = Math.Max(r, Math.Max(g, b));
            float min = Math.Min(r, Math.Min(g, b));
            float diff = max - min;

            if (diff == 0) return 0;

            float hue;
            if (max == r)
                hue = (g - b) / diff % 6;
            else if (max == g)
                hue = (b - r) / diff + 2;
            else
                hue = (r - g) / diff + 4;

            return hue * 60;
        }

        private void UpdateSpotPositions()
        {
            int centerX = Width / 2;
            int centerY = Height / 2;

            switch (currentLayout)
            {
                case LayoutMode.Circular:
                    float baseDistance = Math.Min(Width, Height) * 0.35f;
                    for (int i = 0; i < NumSpotlights; i++)
                    {
                        double angle = spotlightAngles[i];
                        spotX[i] = centerX + (float)(baseDistance * Math.Cos(angle));
                        spotY[i] = centerY + (float)(baseDistance * Math.Sin(angle));
                    }
                    break;

                case LayoutMode.Grid2x4:
                    int cols = 4;
                    int rows = 2;
                    float cellWidth = Width / (cols + 1);
                    float cellHeight = Height / (rows + 1);
                    for (int i = 0; i < NumSpotlights; i++)
                    {
                        int col = i % cols;
                        int row = i / cols;
                        spotX[i] = cellWidth * (col + 1);
                        spotY[i] = cellHeight * (row + 1);
                    }
                    break;

                case LayoutMode.Grid1x8:
                    cols = 8;
                    cellWidth = Width / (cols + 1);
                    for (int i = 0; i < NumSpotlights; i++)
                    {
                        spotX[i] = cellWidth * (i + 1);
                        spotY[i] = Height / 2;
                    }
                    break;

                case LayoutMode.Grid4x2:
                    cols = 2;
                    rows = 4;
                    cellWidth = Width / (cols + 1);
                    cellHeight = Height / (rows + 1);
                    for (int i = 0; i < NumSpotlights; i++)
                    {
                        int col = i % cols;
                        int row = i / cols;
                        spotX[i] = cellWidth * (col + 1);
                        spotY[i] = cellHeight * (row + 1);
                    }
                    break;
            }
        }

        private void DrawSpotlights(Graphics g)
        {
            for (int i = 0; i < NumSpotlights; i++)
            {
                float intensity = smoothIntensities[i];

                float boostedIntensity = Math.Min(1f, intensity * globalBrightnessBoost);
                float displayIntensity = Math.Max(spotMinBrightness[i], boostedIntensity);
                if (!hasSound) displayIntensity = spotMinBrightness[i] * 0.7f;

                float beatPulse = isBeat ? 1.3f : 1.0f;
                float finalIntensity = Math.Min(1.0f, displayIntensity * beatPulse);

                float x = spotX[i];
                float y = spotY[i];

                Color color = spotlightColors[i];

                float brightness = 0.2f + finalIntensity * 1.2f;
                brightness = Math.Min(1.0f, brightness);

                int r = Math.Min(255, (int)(color.R * brightness));
                int gb = Math.Min(255, (int)(color.G * brightness));
                int b = Math.Min(255, (int)(color.B * brightness));
                Color brightColor = Color.FromArgb(r, gb, b);

                if (isRectangular)
                {
                    float width = spotWidth * (0.8f + finalIntensity * 0.4f);
                    float height = spotHeight * (0.8f + finalIntensity * 0.4f);

                    for (int j = 0; j < 3; j++)
                    {
                        int alpha = (int)(120 * finalIntensity * (1 - j / 3f));
                        using (Brush brush = new SolidBrush(Color.FromArgb(alpha, brightColor)))
                        {
                            float offset = j * 5;
                            g.FillRectangle(brush, x - width / 2 - offset, y - height / 2 - offset,
                                           width + offset * 2, height + offset * 2);
                        }
                    }

                    using (Brush brush = new SolidBrush(brightColor))
                    {
                        g.FillRectangle(brush, x - width / 2, y - height / 2, width, height);
                    }

                    using (Pen pen = new Pen(Color.White, 2))
                    {
                        g.DrawRectangle(pen, x - width / 2, y - height / 2, width, height);
                    }
                }
                else
                {
                    float size = spotSize * (0.6f + finalIntensity * 0.5f);

                    for (int j = (int)size; j > 0; j -= Math.Max(8, (int)size / 5))
                    {
                        int alpha = (int)(180 * finalIntensity * (1 - (float)j / size));
                        alpha = Math.Max(10, Math.Min(255, alpha));

                        using (Brush brush = new SolidBrush(Color.FromArgb(alpha, brightColor)))
                        {
                            g.FillEllipse(brush, x - j, y - j, j * 2, j * 2);
                        }
                    }

                    using (Brush brush = new SolidBrush(brightColor))
                    {
                        int coreSize = Math.Max(15, (int)(size / 3));
                        g.FillEllipse(brush, x - coreSize, y - coreSize, coreSize * 2, coreSize * 2);
                    }
                }
            }
        }

        private string GetFreqRangeDisplay(int index)
        {
            int low = freqLowBoundsHz[index];
            int high = freqHighBoundsHz[index];

            string lowStr = low >= 1000 ? $"{low / 1000}.{low % 1000 / 100}кГц" : $"{low}Гц";
            string highStr = high >= 1000 ? $"{high / 1000}.{high % 1000 / 100}кГц" : $"{high}Гц";

            return $"{lowStr} - {highStr}";
        }

        private void LayoutModeCombo_SelectedIndexChanged(object sender, EventArgs e)
        {
            currentLayout = (LayoutMode)layoutModeCombo.SelectedIndex;
            UpdateSpotPositions();
        }

        private void RectangularCheckBox_CheckedChanged(object sender, EventArgs e)
        {
            isRectangular = rectangularCheckBox.Checked;
        }

        private void SpotSizeSlider_Scroll(object sender, EventArgs e)
        {
            int newSize = spotSizeSlider.Value;
            spotSize = newSize;
            if (spotSizeNud != null)
                spotSizeNud.Value = newSize;
            spotWidth = spotSize * 0.8f;
            spotHeight = spotSize * 0.6f;
            if (spotSizeLabel != null)
                spotSizeLabel.Text = newSize.ToString();
        }

        private void ColorNud_ValueChanged(object sender, EventArgs e)
        {
            NumericUpDown nud = sender as NumericUpDown;
            if (nud == null) return;

            int index = (int)nud.Tag;
            float hue = (float)nud.Value / 360f;
            spotlightColors[index] = HSVToColor(hue, 1.0, 1.0);

            if (lowFreqNud[index] != null)
                lowFreqNud[index].ForeColor = spotlightColors[index];
            if (highFreqNud[index] != null)
                highFreqNud[index].ForeColor = spotlightColors[index];
            if (sensitivityNud[index] != null)
                sensitivityNud[index].ForeColor = spotlightColors[index];
            if (minBrightnessNud[index] != null)
                minBrightnessNud[index].ForeColor = spotlightColors[index];
            if (colorPickerNud[index] != null)
                colorPickerNud[index].ForeColor = spotlightColors[index];
            if (levelIndicators[index] != null)
                levelIndicators[index].ForeColor = spotlightColors[index];
            if (currentLevelLabels[index] != null)
                currentLevelLabels[index].ForeColor = spotlightColors[index];
        }

        private void UpdateRangeLabel(int index)
        {
            foreach (Control control in controlsPanel.Controls)
            {
                if (control is Panel panel)
                {
                    foreach (Control child in panel.Controls)
                    {
                        if (child is Label label && label.Name == $"rangeLabel_{index}")
                        {
                            label.Text = GetFreqRangeDisplay(index);
                            return;
                        }
                    }
                }
            }
        }

        private void SaveSettings()
        {
            try
            {
                var settings = new Settings
                {
                    GlobalSensitivity = globalSensitivity,
                    GlobalBrightnessBoost = globalBrightnessBoost,
                    FreqLowBoundsHz = (int[])freqLowBoundsHz.Clone(),
                    FreqHighBoundsHz = (int[])freqHighBoundsHz.Clone(),
                    SpotSensitivity = (float[])spotSensitivity.Clone(),
                    SpotMinBrightness = (float[])spotMinBrightness.Clone(),
                    SpotColorsArgb = spotlightColors.Select(c => c.ToArgb()).ToArray(),
                    SpectrumVisible = spectrumVisible,
                    InfoVisible = infoVisible,
                    LayoutMode = (int)currentLayout,
                    IsRectangular = isRectangular,
                    SpotSize = spotSize,
                    SaveDate = DateTime.Now
                };

                string json = JsonSerializer.Serialize(settings, new JsonSerializerOptions { WriteIndented = true });
                File.WriteAllText(settingsPath, json);

                Console.WriteLine($"✅ Настройки сохранены");
            }
            catch (Exception ex)
            {
                Console.WriteLine($"❌ Ошибка сохранения: {ex.Message}");
            }
        }

        private void LoadSettings()
        {
            if (!File.Exists(settingsPath)) return;

            try
            {
                string json = File.ReadAllText(settingsPath);
                var settings = JsonSerializer.Deserialize<Settings>(json);

                if (settings != null)
                {
                    // Загружаем глобальные настройки
                    globalSensitivity = settings.GlobalSensitivity;
                    globalBrightnessBoost = settings.GlobalBrightnessBoost;

                    if (globalSensitivityNud != null)
                        globalSensitivityNud.Value = (decimal)globalSensitivity;
                    if (globalBrightnessNud != null)
                        globalBrightnessNud.Value = (decimal)globalBrightnessBoost;

                    // Загружаем частоты
                    if (settings.FreqLowBoundsHz != null)
                    {
                        for (int i = 0; i < NumSpotlights && i < settings.FreqLowBoundsHz.Length; i++)
                        {
                            freqLowBoundsHz[i] = Math.Max(MinFreq, Math.Min(MaxFreq, settings.FreqLowBoundsHz[i]));
                            freqHighBoundsHz[i] = Math.Max(freqLowBoundsHz[i] + 1, Math.Min(MaxFreq, settings.FreqHighBoundsHz[i]));
                            spotSensitivity[i] = Math.Max(0.1f, Math.Min(5.0f, settings.SpotSensitivity[i]));
                            spotMinBrightness[i] = Math.Max(0.05f, Math.Min(0.5f, settings.SpotMinBrightness[i]));

                            if (lowFreqNud[i] != null)
                                lowFreqNud[i].Value = freqLowBoundsHz[i];
                            if (highFreqNud[i] != null)
                                highFreqNud[i].Value = freqHighBoundsHz[i];
                            if (sensitivityNud[i] != null)
                                sensitivityNud[i].Value = (decimal)spotSensitivity[i];
                            if (minBrightnessNud[i] != null)
                                minBrightnessNud[i].Value = (decimal)spotMinBrightness[i];

                            UpdateRangeLabel(i);
                        }
                    }

                    // Загружаем цвета
                    if (settings.SpotColorsArgb != null)
                    {
                        for (int i = 0; i < NumSpotlights && i < settings.SpotColorsArgb.Length; i++)
                        {
                            spotlightColors[i] = Color.FromArgb(settings.SpotColorsArgb[i]);
                            if (colorPickerNud[i] != null)
                            {
                                float hue = (float)GetHueFromColor(spotlightColors[i]);
                                colorPickerNud[i].Value = Math.Max(0, Math.Min(360, (decimal)hue));
                                colorPickerNud[i].ForeColor = spotlightColors[i];
                            }
                        }
                    }

                    // Загружаем настройки отображения
                    currentLayout = (LayoutMode)settings.LayoutMode;
                    isRectangular = settings.IsRectangular;
                    spotSize = Math.Max(50, Math.Min(1500, settings.SpotSize));

                    if (layoutModeCombo != null)
                        layoutModeCombo.SelectedIndex = (int)currentLayout;
                    if (rectangularCheckBox != null)
                        rectangularCheckBox.Checked = isRectangular;
                    if (spotSizeSlider != null)
                        spotSizeSlider.Value = (int)spotSize;
                    if (spotSizeNud != null)
                        spotSizeNud.Value = (int)spotSize;
                    if (spotSizeLabel != null)
                        spotSizeLabel.Text = spotSize.ToString();

                    // Обновляем размеры прямоугольных прожекторов
                    spotWidth = spotSize * 0.8f;
                    spotHeight = spotSize * 0.6f;

                    spectrumVisible = settings.SpectrumVisible;
                    infoVisible = settings.InfoVisible;

                    UpdateSpotPositions();

                    Console.WriteLine($"✅ Настройки загружены. Размер прожектора: {spotSize}");
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"❌ Ошибка загрузки: {ex.Message}");
            }
        }

        private void UpdateLevelIndicators()
        {
            for (int i = 0; i < NumSpotlights; i++)
            {
                if (levelIndicators[i] != null)
                {
                    int level = (int)(smoothIntensities[i] * 100);
                    levelIndicators[i].Value = level;
                    if (currentLevelLabels[i] != null)
                    {
                        currentLevelLabels[i].Text = $"{level}%";
                    }
                }
            }
        }

        private void LowFreqNud_ValueChanged(object sender, EventArgs e)
        {
            NumericUpDown nud = sender as NumericUpDown;
            if (nud == null) return;

            int index = (int)nud.Tag;
            int newValue = (int)nud.Value;

            if (newValue >= freqHighBoundsHz[index])
            {
                newValue = freqHighBoundsHz[index] - 1;
                if (newValue < MinFreq) newValue = MinFreq;
                nud.Value = newValue;
            }

            freqLowBoundsHz[index] = newValue;
            UpdateRangeLabel(index);
        }

        private void HighFreqNud_ValueChanged(object sender, EventArgs e)
        {
            NumericUpDown nud = sender as NumericUpDown;
            if (nud == null) return;

            int index = (int)nud.Tag;
            int newValue = (int)nud.Value;

            if (newValue <= freqLowBoundsHz[index])
            {
                newValue = freqLowBoundsHz[index] + 1;
                if (newValue > MaxFreq) newValue = MaxFreq;
                nud.Value = newValue;
            }

            freqHighBoundsHz[index] = newValue;
            UpdateRangeLabel(index);
        }

        private void SensitivityNud_ValueChanged(object sender, EventArgs e)
        {
            NumericUpDown nud = sender as NumericUpDown;
            if (nud == null) return;

            int index = (int)nud.Tag;
            spotSensitivity[index] = (float)nud.Value;
        }

        private void MinBrightnessNud_ValueChanged(object sender, EventArgs e)
        {
            NumericUpDown nud = sender as NumericUpDown;
            if (nud == null) return;

            int index = (int)nud.Tag;
            spotMinBrightness[index] = (float)nud.Value;
        }

        private void GlobalSensitivityNud_ValueChanged(object sender, EventArgs e)
        {
            globalSensitivity = (float)globalSensitivityNud.Value;
        }

        private void GlobalBrightnessNud_ValueChanged(object sender, EventArgs e)
        {
            globalBrightnessBoost = (float)globalBrightnessNud.Value;
        }

        private void SaveButton_Click(object sender, EventArgs e)
        {
            SaveSettings();
            MessageBox.Show("Настройки сохранены!", "Успех", MessageBoxButtons.OK, MessageBoxIcon.Information);
        }

        private void LoadButton_Click(object sender, EventArgs e)
        {
            LoadSettings();
            MessageBox.Show("Настройки загружены!", "Успех", MessageBoxButtons.OK, MessageBoxIcon.Information);
        }

        private void ResetButton_Click(object sender, EventArgs e)
        {
            globalSensitivityNud.Value = 3.0m;
            globalBrightnessNud.Value = 2.5m;

            for (int i = 0; i < NumSpotlights; i++)
            {
                double logMin = Math.Log10(MinFreq);
                double logMax = Math.Log10(MaxFreq);
                double logLow = logMin + (logMax - logMin) * i / NumSpotlights;
                double logHigh = logMin + (logMax - logMin) * (i + 1) / NumSpotlights;

                freqLowBoundsHz[i] = (int)Math.Pow(10, logLow);
                freqHighBoundsHz[i] = (int)Math.Pow(10, logHigh);

                if (lowFreqNud[i] != null)
                    lowFreqNud[i].Value = freqLowBoundsHz[i];
                if (highFreqNud[i] != null)
                    highFreqNud[i].Value = freqHighBoundsHz[i];

                if (sensitivityNud[i] != null)
                    sensitivityNud[i].Value = 1.0m;
                spotSensitivity[i] = 1.0f;

                if (minBrightnessNud[i] != null)
                    minBrightnessNud[i].Value = 0.12m;
                spotMinBrightness[i] = 0.12f;

                double hue = (double)i / NumSpotlights;
                spotlightColors[i] = HSVToColor(hue, 1.0, 1.0);
                if (colorPickerNud[i] != null)
                {
                    colorPickerNud[i].Value = (decimal)(hue * 360);
                    colorPickerNud[i].ForeColor = spotlightColors[i];
                }

                UpdateRangeLabel(i);
            }
            freqHighBoundsHz[NumSpotlights - 1] = MaxFreq;
            if (highFreqNud[NumSpotlights - 1] != null)
                highFreqNud[NumSpotlights - 1].Value = MaxFreq;

            currentLayout = LayoutMode.Circular;
            isRectangular = false;
            spotSize = 120f;

            if (layoutModeCombo != null)
                layoutModeCombo.SelectedIndex = 0;
            if (rectangularCheckBox != null)
                rectangularCheckBox.Checked = false;
            if (spotSizeSlider != null)
                spotSizeSlider.Value = 120;
            if (spotSizeNud != null)
                spotSizeNud.Value = 120;
            if (spotSizeLabel != null)
                spotSizeLabel.Text = "120";

            spotWidth = spotSize * 0.8f;
            spotHeight = spotSize * 0.6f;

            UpdateSpotPositions();
        }

        private void CreateMainBuffer()
        {
            if (mainBuffer != null)
                mainBuffer.Dispose();

            if (Width <= 0 || Height <= 0) return;

            mainBuffer = new Bitmap(Width, Height);
            mainGraphics = Graphics.FromImage(mainBuffer);
            mainGraphics.SmoothingMode = SmoothingMode.AntiAlias;
            mainGraphics.CompositingQuality = CompositingQuality.HighQuality;

            DrawStaticBackground();
            UpdateSpotPositions();
        }

        private void DrawStaticBackground()
        {
            if (mainGraphics == null) return;

            mainGraphics.Clear(Color.Black);

            int centerX = Width / 2;
            int centerY = Height / 2;

            Random starRand = new Random(42);
            for (int i = 0; i < 200; i++)
            {
                int x = starRand.Next(Width);
                int y = starRand.Next(Height);
                int radius = starRand.Next(1, 2);
                int brightness = starRand.Next(60, 180);
                using (Brush brush = new SolidBrush(Color.FromArgb(brightness, 255, 255, 255)))
                {
                    mainGraphics.FillEllipse(brush, x - radius, y - radius, radius * 2, radius * 2);
                }
            }

            using (Pen pen = new Pen(Color.FromArgb(40, 100, 100, 100), 1))
            {
                for (int r = 1; r <= 4; r++)
                {
                    int radius = Math.Min(Width, Height) / 6 * r;
                    mainGraphics.DrawEllipse(pen, centerX - radius, centerY - radius, radius * 2, radius * 2);
                }
            }
        }

        private void InitializeSpotlights()
        {
            spotlightAngles = new double[NumSpotlights];
            for (int i = 0; i < NumSpotlights; i++)
            {
                spotlightAngles[i] = (Math.PI * 2 / NumSpotlights) * i;
            }
        }

        private void InitializeAudioLoopbackWithSilence()
        {
            try
            {
                var enumerator = new MMDeviceEnumerator();
                var renderDevices = enumerator.EnumerateAudioEndPoints(DataFlow.Render, DeviceState.Active);

                MMDevice selectedDevice = null;
                foreach (var device in renderDevices)
                {
                    if (selectedDevice == null)
                        selectedDevice = device;
                }

                if (selectedDevice != null)
                {
                    currentDeviceName = selectedDevice.FriendlyName;
                    Console.WriteLine($"\n✅ ВЫБРАНО: {currentDeviceName}");

                    var waveFormat = new WaveFormat(44100, 16, 2);
                    silenceProvider = new SilenceProvider(waveFormat);
                    silencePlayer = new WasapiOut(selectedDevice, AudioClientShareMode.Shared, false, 100);
                    silencePlayer.Init(silenceProvider);
                    silencePlayer.Play();

                    wasapiCapture = new WasapiLoopbackCapture(selectedDevice);
                    wasapiCapture.WaveFormat = waveFormat;
                    wasapiCapture.DataAvailable += OnDataAvailable;
                    wasapiCapture.RecordingStopped += OnRecordingStopped;
                    wasapiCapture.StartRecording();

                    Console.WriteLine($"✅ Захват запущен!");
                    isAudioInitialized = true;
                }
                else
                {
                    throw new Exception("Нет доступных устройств воспроизведения!");
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"\n❌ ОШИБКА: {ex.Message}");
                currentDeviceName = "ОШИБКА!";
                isAudioInitialized = false;

                MessageBox.Show($"Не удалось захватить звук!\n\n{ex.Message}\n\n" +
                              "Запустите программу от имени администратора!",
                              "Ошибка", MessageBoxButtons.OK, MessageBoxIcon.Warning);
            }
        }

        private void OnDataAvailable(object sender, WaveInEventArgs e)
        {
            lastDataReceived = DateTime.Now;

            float[] samples = new float[e.BytesRecorded / 2];
            for (int i = 0; i < samples.Length && i < audioBuffer.Length; i++)
            {
                samples[i] = BitConverter.ToInt16(e.Buffer, i * 2) / 32768f;
            }

            lock (audioBuffer)
            {
                int take = Math.Min(samples.Length, audioBuffer.Length);
                Array.Copy(samples, audioBuffer, take);
                if (take < audioBuffer.Length)
                    Array.Clear(audioBuffer, take, audioBuffer.Length - take);
            }
        }

        private void OnRecordingStopped(object sender, StoppedEventArgs e)
        {
            Console.WriteLine("Запись остановлена");
        }

        private int FreqToIndex(int freqHz, int fftLength)
        {
            double maxFreqFFT = 22050;
            return (int)((double)freqHz / maxFreqFFT * fftLength);
        }

        private void AnalyzeAudio()
        {
            if (!isAudioInitialized) return;
            if ((DateTime.Now - lastDataReceived).TotalSeconds > 2) return;

            float[] monoData;
            lock (audioBuffer)
            {
                monoData = (float[])audioBuffer.Clone();
            }

            if (monoData.Length == 0) return;

            float rms = 0;
            for (int i = 0; i < monoData.Length; i++)
            {
                rms += monoData[i] * monoData[i];
            }
            rms = (float)Math.Sqrt(rms / monoData.Length);

            volumeHistory[volumeIndex] = rms;
            volumeIndex = (volumeIndex + 1) % volumeHistory.Length;

            float avg = volumeHistory.Average();
            beatThreshold = avg * 1.5f;
            isBeat = rms > beatThreshold && rms > 0.02f;

            Complex[] complexData = new Complex[monoData.Length];
            for (int i = 0; i < monoData.Length; i++)
            {
                complexData[i] = new Complex(monoData[i], 0);
            }

            FFT(complexData, false);

            for (int i = 0; i < fftData.Length && i < complexData.Length; i++)
            {
                fftData[i] = (float)complexData[i].Magnitude / chunkSize;
            }

            for (int i = 0; i < NumSpotlights; i++)
            {
                int fftLength = fftData.Length;
                int startIdx = FreqToIndex(freqLowBoundsHz[i], fftLength);
                int endIdx = FreqToIndex(freqHighBoundsHz[i], fftLength);

                startIdx = Math.Max(0, Math.Min(startIdx, fftLength - 1));
                endIdx = Math.Max(startIdx + 1, Math.Min(endIdx, fftLength));

                float intensity = 0;
                for (int j = startIdx; j < endIdx; j++)
                {
                    intensity += fftData[j];
                }

                float baseIntensity = (intensity / (endIdx - startIdx)) * (8f * globalSensitivity * spotSensitivity[i]);
                intensity = Math.Min(1f, baseIntensity);
                intensity = (float)Math.Pow(intensity, 0.8f);

                spotlightIntensities[i] = intensity;
            }

            for (int i = 0; i < NumSpotlights; i++)
            {
                smoothIntensities[i] = smoothIntensities[i] * 0.3f + spotlightIntensities[i] * 0.7f;
            }

            UpdateLevelIndicators();

            totalIntensity = Math.Min(1f, rms * (10f * globalSensitivity));

            bool hasRealSound = totalIntensity > 0.008f;
            if (hasRealSound)
            {
                hasSound = true;
                lastSoundTime = DateTime.Now;
            }
            else if ((DateTime.Now - lastSoundTime).TotalSeconds > 1)
            {
                hasSound = false;
            }

            if (isBeat && hasRealSound && totalIntensity > 0.05f)
            {
                int numParticles = (int)(totalIntensity * 15);
                for (int i = 0; i < Math.Min(numParticles, 8); i++)
                {
                    int spotlightIdx = random.Next(NumSpotlights);
                    float x = spotX[spotlightIdx];
                    float y = spotY[spotlightIdx];

                    particles.Add(new Particle
                    {
                        X = x,
                        Y = y,
                        VX = (float)(random.NextDouble() * 10 - 5),
                        VY = (float)(random.NextDouble() * 10 - 5),
                        Life = 1f,
                        Color = spotlightColors[spotlightIdx],
                        Size = (int)(5 + smoothIntensities[spotlightIdx] * 10)
                    });
                }
            }

            for (int i = particles.Count - 1; i >= 0; i--)
            {
                particles[i].X += particles[i].VX;
                particles[i].Y += particles[i].VY;
                particles[i].Life -= 0.025f;

                if (particles[i].Life <= 0 ||
                    particles[i].X < 0 || particles[i].X > Width ||
                    particles[i].Y < 0 || particles[i].Y > Height)
                {
                    particles.RemoveAt(i);
                }
            }
        }

        private void DrawSpectrum(Graphics g)
        {
            if (!spectrumVisible) return;
            if (g == null) return;
            if (fftData == null || fftData.Length == 0) return;

            int specWidth = 400;
            int specHeight = 150;
            int specX = Width - specWidth - 10;
            int specY = Height - specHeight - 30;

            if (specY < 0) specY = 10;
            if (specX < 0) specX = 10;

            using (Brush bgBrush = new SolidBrush(Color.FromArgb(180, 0, 0, 0)))
            {
                g.FillRectangle(bgBrush, specX, specY, specWidth, specHeight);
            }

            using (Pen borderPen = new Pen(Color.FromArgb(150, 0, 255, 0), 1))
            {
                g.DrawRectangle(borderPen, specX, specY, specWidth, specHeight);
            }

            using (Font font = new Font("Segoe UI", 8, FontStyle.Bold))
            using (Brush textBrush = new SolidBrush(Color.FromArgb(200, 0, 255, 0)))
            {
                g.DrawString("СПЕКТРОГРАММА", font, textBrush, specX + 10, specY + 5);
            }

            float maxVal = 0.001f;
            for (int i = 0; i < fftData.Length; i++)
            {
                if (fftData[i] > maxVal) maxVal = fftData[i];
            }

            if (maxVal < 0.001f) maxVal = 0.001f;

            int barCount = 32;
            int barWidth = (specWidth - 20) / barCount;
            int chartHeight = specHeight - 40;
            int chartBottom = specY + specHeight - 12;

            for (int i = 0; i < barCount && i < fftData.Length; i++)
            {
                float value = 0;
                int samplesPerBar = Math.Max(1, fftData.Length / barCount);
                int startIdx = i * samplesPerBar;
                int endIdx = Math.Min(startIdx + samplesPerBar, fftData.Length);

                for (int j = startIdx; j < endIdx; j++)
                {
                    value += fftData[j];
                }
                value /= (endIdx - startIdx);

                float normalizedValue = value / maxVal;
                normalizedValue = Math.Min(1f, normalizedValue * 3f);
                normalizedValue = (float)Math.Pow(normalizedValue, 0.7f);

                int barHeight = (int)(normalizedValue * chartHeight);
                barHeight = Math.Max(2, Math.Min(chartHeight, barHeight));

                double hue = (double)i / barCount;
                Color barColor = HSVToColor(hue, 1.0, 0.8 + normalizedValue * 0.2);

                using (Brush barBrush = new SolidBrush(barColor))
                {
                    g.FillRectangle(barBrush, specX + 10 + i * barWidth,
                                   chartBottom - barHeight,
                                   barWidth - 1, barHeight);
                }
            }

            using (Font font = new Font("Segoe UI", 6))
            using (Brush textBrush = new SolidBrush(Color.FromArgb(150, 200, 200, 200)))
            {
                string[] labels = { "20Hz", "50Hz", "100Hz", "200Hz", "500Hz", "1kHz", "2kHz", "5kHz", "10kHz", "20kHz" };
                int[] positions = { 0, 3, 6, 10, 14, 18, 22, 26, 29, 31 };

                for (int i = 0; i < labels.Length && i < positions.Length; i++)
                {
                    int x = specX + 10 + positions[i] * barWidth;
                    if (x + 30 < specX + specWidth)
                    {
                        g.DrawString(labels[i], font, textBrush, x, chartBottom + 2);
                    }
                }
            }
        }

        private void UpdateSpotlightsBrightness()
        {
            if (mainBuffer == null) return;

            using (Graphics tempGraphics = Graphics.FromImage(mainBuffer))
            {
                tempGraphics.CompositingMode = CompositingMode.SourceOver;
                tempGraphics.SmoothingMode = SmoothingMode.AntiAlias;

                RestoreBackground();
                DrawSpotlights(tempGraphics);
                DrawParticles(tempGraphics);
                DrawSpectrum(tempGraphics);

                if (infoVisible)
                {
                    DrawTextInfo(tempGraphics);
                }
            }
        }

        private void RestoreBackground()
        {
            if (mainBuffer == null) return;

            using (Graphics bgGraphics = Graphics.FromImage(mainBuffer))
            {
                bgGraphics.Clear(Color.Black);

                int centerX = Width / 2;
                int centerY = Height / 2;

                Random starRand = new Random(42);
                for (int i = 0; i < 200; i++)
                {
                    int x = starRand.Next(Width);
                    int y = starRand.Next(Height);
                    int radius = starRand.Next(1, 2);
                    int brightness = starRand.Next(60, 180);
                    using (Brush brush = new SolidBrush(Color.FromArgb(brightness, 255, 255, 255)))
                    {
                        bgGraphics.FillEllipse(brush, x - radius, y - radius, radius * 2, radius * 2);
                    }
                }

                using (Pen pen = new Pen(Color.FromArgb(40, 100, 100, 100), 1))
                {
                    for (int r = 1; r <= 4; r++)
                    {
                        int radius = Math.Min(Width, Height) / 6 * r;
                        bgGraphics.DrawEllipse(pen, centerX - radius, centerY - radius, radius * 2, radius * 2);
                    }
                }
            }
        }

        private void DrawParticles(Graphics g)
        {
            if (g == null) return;

            foreach (var particle in particles)
            {
                int alpha = (int)(200 * particle.Life);
                alpha = Math.Max(0, Math.Min(255, alpha));
                using (Brush brush = new SolidBrush(Color.FromArgb(alpha, particle.Color)))
                {
                    g.FillEllipse(brush, particle.X - particle.Size, particle.Y - particle.Size,
                                 particle.Size * 2, particle.Size * 2);
                }
            }
        }

        private void DrawTextInfo(Graphics g)
        {
            if (g == null) return;

            using (Font font = new Font("Segoe UI", 8))
            using (Brush whiteBrush = new SolidBrush(Color.FromArgb(200, 255, 255, 255)))
            using (Brush greenBrush = new SolidBrush(Color.FromArgb(200, 0, 255, 0)))
            using (Brush redBrush = new SolidBrush(Color.FromArgb(200, 255, 0, 0)))
            {
                g.DrawString($"FPS: {currentFps:F0}", font, greenBrush, Width - 100, 5);

                string status = hasSound ? "● ЗВУК ЕСТЬ" : "○ НЕТ ЗВУКА";
                Brush statusBrush = hasSound ? greenBrush : redBrush;
                g.DrawString(status, font, statusBrush, Width - 120, 25);

                string controls = "H - Панель | S - Спектр | I - Инфо | R - Частицы | ESC - Выход";
                g.DrawString(controls, font, whiteBrush, 10, Height - 20);
            }
        }

        private void OnTimerTick(object sender, EventArgs e)
        {
            if (!isRunning) return;

            AnalyzeAudio();
            UpdateSpotlightsBrightness();

            frameCount++;
            if ((DateTime.Now - lastFpsUpdate).TotalSeconds >= 1)
            {
                currentFps = frameCount / (float)(DateTime.Now - lastFpsUpdate).TotalSeconds;
                frameCount = 0;
                lastFpsUpdate = DateTime.Now;
            }

            Invalidate();
        }

        private void Form1_Paint(object sender, PaintEventArgs e)
        {
            if (mainBuffer != null && e.Graphics != null)
            {
                e.Graphics.DrawImage(mainBuffer, 0, 0);
            }
        }

        private void Form1_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.KeyCode == Keys.Escape)
            {
                Close();
            }
            else if (e.KeyCode == Keys.R)
            {
                particles.Clear();
            }
            else if (e.KeyCode == Keys.H)
            {
                controlsVisible = !controlsVisible;
                if (controlsPanel != null)
                    controlsPanel.Visible = controlsVisible;
            }
            else if (e.KeyCode == Keys.S)
            {
                spectrumVisible = !spectrumVisible;
            }
            else if (e.KeyCode == Keys.I)
            {
                infoVisible = !infoVisible;
            }
        }

        private void Form1_Resize(object sender, EventArgs e)
        {
            CreateMainBuffer();
            UpdateSpotPositions();
        }

        private void Form1_FormClosing(object sender, FormClosingEventArgs e)
        {
            SaveSettings();
            isRunning = false;

            if (silencePlayer != null)
            {
                silencePlayer.Stop();
                silencePlayer.Dispose();
            }
            if (wasapiCapture != null)
            {
                wasapiCapture.StopRecording();
                wasapiCapture.Dispose();
            }
            if (mainBuffer != null)
                mainBuffer.Dispose();
            if (mainGraphics != null)
                mainGraphics.Dispose();
        }

        private Color HSVToColor(double hue, double saturation, double value)
        {
            int hi = Convert.ToInt32(Math.Floor(hue * 6)) % 6;
            double f = hue * 6 - Math.Floor(hue * 6);

            double p = value * (1 - saturation);
            double q = value * (1 - f * saturation);
            double t = value * (1 - (1 - f) * saturation);

            double r = 0, g = 0, b = 0;

            switch (hi)
            {
                case 0: r = value; g = t; b = p; break;
                case 1: r = q; g = value; b = p; break;
                case 2: r = p; g = value; b = t; break;
                case 3: r = p; g = q; b = value; break;
                case 4: r = t; g = p; b = value; break;
                case 5: r = value; g = p; b = q; break;
            }

            return Color.FromArgb((int)(r * 255), (int)(g * 255), (int)(b * 255));
        }

        private void FFT(Complex[] buffer, bool inverse)
        {
            int n = buffer.Length;
            if (n == 1) return;

            Complex[] even = new Complex[n / 2];
            Complex[] odd = new Complex[n / 2];

            for (int i = 0; i < n / 2; i++)
            {
                even[i] = buffer[2 * i];
                odd[i] = buffer[2 * i + 1];
            }

            FFT(even, inverse);
            FFT(odd, inverse);

            float angle = (float)(2 * Math.PI / n * (inverse ? -1 : 1));
            Complex w = new Complex(1, 0);
            Complex wn = new Complex((float)Math.Cos(angle), (float)Math.Sin(angle));

            for (int i = 0; i < n / 2; i++)
            {
                Complex t = w * odd[i];
                buffer[i] = even[i] + t;
                buffer[i + n / 2] = even[i] - t;
                w *= wn;
            }
        }
    }

    public class Particle
    {
        public float X { get; set; }
        public float Y { get; set; }
        public float VX { get; set; }
        public float VY { get; set; }
        public float Life { get; set; }
        public Color Color { get; set; }
        public int Size { get; set; }
    }
}