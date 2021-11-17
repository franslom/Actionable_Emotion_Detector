package com.empatica.sample;

import android.Manifest;
import android.app.Activity;
import android.app.Dialog;
import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothDevice;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.media.AudioFormat;
import android.media.AudioManager;
import android.media.AudioRecord;
import android.media.MediaPlayer;
import android.media.MediaRecorder;
import android.net.Uri;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.provider.Settings;
import android.speech.tts.TextToSpeech;
import android.support.annotation.FloatRange;
import android.support.annotation.NonNull;
import android.support.design.widget.Snackbar;
import android.support.v4.app.ActivityCompat;
import android.support.v4.content.ContextCompat;
import android.support.v7.app.AlertDialog;
import android.support.v7.app.AppCompatActivity;
import android.text.TextUtils;
import android.text.format.Time;
import android.util.Base64;
import android.util.Log;
import android.util.SparseArray;
import android.view.View;
import android.view.WindowManager;
import android.widget.Button;
import android.widget.EditText;
import android.widget.RelativeLayout;
import android.widget.TextView;
import android.widget.Toast;

import com.empatica.empalink.ConnectionNotAllowedException;
import com.empatica.empalink.EmpaDeviceManager;
import com.empatica.empalink.config.EmpaSensorStatus;
import com.empatica.empalink.config.EmpaSensorType;
import com.empatica.empalink.config.EmpaStatus;
import com.empatica.empalink.delegate.EmpaDataDelegate;
import com.empatica.empalink.delegate.EmpaStatusDelegate;
import com.empatica.sample.ui.camera.CameraSourcePreview;
import com.empatica.sample.ui.camera.GraphicOverlay;
import com.google.android.gms.common.ConnectionResult;
import com.google.android.gms.common.GoogleApiAvailability;
import com.google.android.gms.vision.CameraSource;
import com.google.android.gms.vision.MultiProcessor;
import com.google.android.gms.vision.Tracker;
import com.google.android.gms.vision.face.Face;
import com.google.android.gms.vision.face.FaceDetector;


import java.io.BufferedOutputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Calendar;
import java.util.Locale;
import java.util.Vector;

import edu.emory.mathcs.jtransforms.fft.DoubleFFT_1D;

import static java.lang.Math.abs;
import static java.lang.Math.log;
import static java.lang.Math.sqrt;


public class MainActivity extends AppCompatActivity implements EmpaDataDelegate, EmpaStatusDelegate {

    //***Variables to connect the E4****//
    private static final int REQUEST_ENABLE_BT = 1;
    private static final int REQUEST_PERMISSION_ACCESS_COARSE_LOCATION = 1;
    private static final long STREAMING_TIME = 216000000; // Stops streaming 10 seconds after connection /// 6 hours
    private static final String EMPATICA_API_KEY = "4f6e0427bda8425d9f31fc9b02874af9"; // TODO insert your API Key here
    private EmpaDeviceManager deviceManager = null;



    //***TextView Variables to show current state***//
    private TextView accel_xLabel;
    private TextView accel_yLabel;
    private TextView accel_zLabel;
    //private TextView bvpLabel;
    private TextView edaLabel;
    //private TextView ibiLabel;
    //private TextView temperatureLabel;
    private TextView batteryLabel;
    private TextView statusLabel;
    private TextView deviceNameLabel;
    private RelativeLayout dataCnt;


    //////********Franci: TextView variables********////////
    private TextView TextView_baseline;
    //private TextView TextView_sax
    //private TextView TextView_initial_time;
    private TextView TextView_physical_activity;
    private TextView TextView_stress;
    private TextView TextView_subjects;
    private TextView TextView_audio;




    ///******EDA Variables***************///



    ///******EDA Variables***************///
    private Vector<Float> eda_vector;
    private Vector<Float> eda_vector_baseline;
    private Vector<Float> eda_vector_baseline_filtered;
    private Vector<Float> eda_vector_window;
    private boolean eda_is_baseline;
    private float eda_baseline;
    private float eda_baseline_sd;
    private int eda_min_baseline;
    private int eda_last_min;
    private int eda_count;




    ///******Time variables to save the start of the session.
    private int initial_sec;
    private int initial_min;
    private int initial_hou;


    private int last_minute;


    //*********ACC Variables***********//
    private Vector<Float> magnitude_by_seconds;
    private Vector<Float> general_magnitude;
    private int seconds_acc;
    private int last_second;




    ///VARIABLES DEL EXPERIMENTO
    private int eda_number_log;
    private int eda_k;
    private int experiment_time;
    private int experiment_count;
    private float b_1;
    private float b_2;
    private float b_3;
    private float b_4;


    ////VARIABLES of SOFTWARE SERVICE
    private Vector<String> service_time;
    private TextToSpeech speaker;
    String message_1;
    String message_2;
    String message_3;
    String message_4;
    String message_5;


    /////VARIABLES FOR AUDIO AMPLITUDE
    private AudioRecord recorder;
    //16 bit per campione in mono
    private final static int RECORDER_AUDIO_ENCODING = AudioFormat.ENCODING_PCM_16BIT;
    private final static int RECORDER_CHANNELS = AudioFormat.CHANNEL_IN_MONO;
    private final static int RECORDER_SAMPLERATE = 44100;
    private final static int BYTES_PER_ELEMENT = 2;
    private final static int BLOCK_SIZE = AudioRecord.getMinBufferSize(
            RECORDER_SAMPLERATE, RECORDER_CHANNELS, RECORDER_AUDIO_ENCODING)
            / BYTES_PER_ELEMENT;
    private final static int BLOCK_SIZE_FFT = 1764;
    private final static double FREQRESOLUTION = ((double) RECORDER_SAMPLERATE)
            / BLOCK_SIZE_FFT;
    private Thread recordingThread = null;
    private boolean isRecording = false;
    private DoubleFFT_1D fft = null;
    private double filter = 0;
    private double[] weightedA = new double[BLOCK_SIZE_FFT];
    private float [] THIRD_OCTAVE = {16, 20, 25, 31.5f, 40, 50, 63, 80, 100, 125, 160, 200, 250, 315, 400, 500,
            630, 800, 1000, 1250, 1600, 2000, 2500, 3150, 4000, 5000, 6300, 8000, 10000, 12500, 16000, 20000};
    double linearFftAGlobalRunning = 0;
    private long fftCount = 0;
    private double dbFftAGlobalRunning;
    private float[] dbBandRunning = new float[THIRD_OCTAVE.length];
    private float[] linearBandRunning = new float[THIRD_OCTAVE.length];
    private double dbATimeDisplay;
    private float dbFftTimeDisplay[] = new float[BLOCK_SIZE_FFT / 2];
    private float[] linearBandTimeDisplay = new float[THIRD_OCTAVE.length];




    ///******VARIABLES FOR CAMERA****/////
    private static final String TAG = "Actionable Emotion Detector";
    private CameraSource mCameraSource = null;
    private CameraSourcePreview mPreview;
    private GraphicOverlay mGraphicOverlay;
    private static final int RC_HANDLE_GMS = 9001;
    // permission request codes need to be < 256
    private static final int RC_HANDLE_CAMERA_PERM = 2;






    ////Varibles de cada funcion
    private Calendar c_GSR;
    private int tmp_hour_GSR;{}
    private int tmp_min_GSR;
    private int tmp_sec_GSR;
    private int tmp_sax_sensors;

    private Calendar c_ACC;
    private int seconds_ACC;
    private int minute_ACC;
    private int hour_ACC;



    private float a_x_ACC;
    private float a_y_ACC;
    private float a_z_ACC;
    private float tmp_ACC;


    private Calendar c_microphone;
    private int seconds_microphone;
    private int minute_microphone;
    private int hour_microphone;
    private int last_second_microphone;
    private boolean is_connecting;
    private int count_seconds_microphone;









    ////**********************************//////////
    ////**********************************//////////
    ////**********************************//////////
    //// VARIABLES FOR ACTIONABLE EMOTION DETECTION/
    ////**********************************//////////
    ////**********************************//////////

    private Vector<Integer> sax_vector;
    private Vector<String> sax_vector_times;

    private Vector<Float> physical_activity_vector;
    private Vector<String> physical_activity_vector_times;

    private Vector<Float> microphone_vector;
    private Vector<String> microphone_vector_times;

    private Vector<Integer> subjects_vector;
    private Vector<String> subjects_vector_times;


    private Float microphone_tmp_sum;
    private int last_minute_microphone;
    private int microphone_tmp_sum_count;
    private boolean is_conversation;
    private boolean is_noise;

    private int current_number_of_subject;


    private short physical_activity;
    private boolean stress_state;
    private boolean was_stressed_by_service;
    private short count_service;
    private String subject_name;
    private String subject_age;
    private String subject_gender;
    private String subject_occupation;

    private  boolean lock_physical_activity;
    private  boolean lock_noise;
    private  boolean lock_conversation;
    private  boolean lock_emotional_trigger;

    private Vector<Float> EDA_vector_emotional_trigger;
    private int eda_count_emotional_trigger;
    private float e_cut;
    private String type_of_emotional_trigger;
    private TextView TextView_emotional_trigger;





    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_main);

        AlertDialog.Builder mBuilder=new AlertDialog.Builder(MainActivity.this);
        final View mView=getLayoutInflater().inflate(R.layout.activity_profile,null);
        final EditText mName=(EditText) mView.findViewById(R.id.editText_name);
        final EditText mAge=(EditText) mView.findViewById(R.id.editText_age);
        final EditText mGender=(EditText) mView.findViewById(R.id.editText_gender);
        final EditText mOccupation=(EditText) mView.findViewById(R.id.editText_occupation);
        Button mProfile=(Button) mView.findViewById(R.id.button_profile);
        mBuilder.setView(mView);
        final AlertDialog dialog=mBuilder.create();
        mProfile.setOnClickListener(new View.OnClickListener() {
                                        @Override
                                        public void onClick(View view) {
                                            if(!mName.getText().toString().isEmpty()&&!mAge.getText().toString().isEmpty()&&!mGender.getText().toString().isEmpty()&&!mOccupation.getText().toString().isEmpty()) {
                                                Log.i("Subject Profile: ", mName.getText().toString());
                                                subject_name=mName.getText().toString();
                                                subject_age=mAge.getText().toString();
                                                subject_gender=mGender.getText().toString();
                                                subject_occupation=mOccupation.getText().toString();
                                                dialog.dismiss();
                                            }
                                        }
                                    });
        dialog.show();

        // Initialize vars that reference UI components
        statusLabel = (TextView) findViewById(R.id.status);
        dataCnt = (RelativeLayout) findViewById(R.id.dataArea);
        accel_xLabel = (TextView) findViewById(R.id.accel_x);
        accel_yLabel = (TextView) findViewById(R.id.accel_y);
        accel_zLabel = (TextView) findViewById(R.id.accel_z);
        //bvpLabel = (TextView) findViewById(R.id.bvp);
        edaLabel = (TextView) findViewById(R.id.eda);
        //ibiLabel = (TextView) findViewById(R.id.ibi);
        //temperatureLabel = (TextView) findViewById(R.id.temperature);
        batteryLabel = (TextView) findViewById(R.id.battery);
        deviceNameLabel = (TextView) findViewById(R.id.deviceName);

        ///Franci: Our operations
        TextView_baseline=(TextView)findViewById(R.id.TextView_baseline);
        TextView_physical_activity=(TextView) findViewById(R.id.textView_physical_activity);
        TextView_stress=(TextView)findViewById(R.id.textView_stress);
        TextView_subjects=(TextView)findViewById(R.id.textView_subjects);
        TextView_audio=(TextView)findViewById(R.id.textView_audio);




        sax_vector=new Vector<Integer>();
        ///*****Declaration of EDA variables************///
        eda_vector=new Vector<Float>();
        eda_vector_window=new Vector<Float>();
        eda_vector_baseline=new Vector<Float>();
        eda_vector_baseline_filtered=new Vector<Float>();
        //eda_30s_sax=new Vector<Integer>();
        eda_baseline=0;
        eda_is_baseline=false;
        eda_min_baseline=15;
        eda_count=0;
        b_1= (float) -0.84;
        b_2= (float) -0.25;
        b_3= (float) 0.25;
        b_4= (float) 0.84;


        ////Settings of the Experiment
        experiment_time=75;
        experiment_count=0;
        eda_k=3;
        eda_number_log=240;


        ///******declaration of ACC variables**********///
        magnitude_by_seconds=new Vector<Float>();
        general_magnitude=new Vector<Float>();
        seconds_acc=0;

        //****Service variables declaration
        message_1 ="It is time to take your pill. Your health could worsen if you do not take your medicines.";
        message_2 = "It is time to take your pill. You should take your pill remember that you committed to improve your health.";
        message_3 = "It is time to take your pill. You should take your pill remember that you committed to improve your health. It is time to take your pill. You should take your pill remember that you committed to improve your health. It is time to take your pill. You should take your pill remember that you committed to improve your health.";
        message_4 = "It is time to take your pill. You must take your pill for your well-being.";
        message_5 = "It is time to take your pill. You must take your pill for your well-being. It is time to take your pill. You must take your pill for your well-being. It is time to take your pill. You must take your pill for your well-being. It is time to take your pill. You must take your pill for your well-being. It is time to take your pill. You must take your pill for your well-being. ";

        speaker=new TextToSpeech(getApplicationContext(), new TextToSpeech.OnInitListener() {
            @Override
            public void onInit(int status) {
                if(status != TextToSpeech.ERROR) {
                    speaker.setLanguage(Locale.UK);
                }
            }
        });



        ////****Declaration of Audio variables*****////
        precalculateWeightedA();
        startRecording(0, 25, 25);


        ///****Declaration of CAMERA VARIABLES****////
        mPreview = (CameraSourcePreview) findViewById(R.id.preview);
        mGraphicOverlay = (GraphicOverlay) findViewById(R.id.faceOverlay);

        // Check for the camera permission before accessing the camera.  If the
        // permission is not granted yet, request permission.
        int rc = ActivityCompat.checkSelfPermission(this, Manifest.permission.CAMERA);
        if (rc == PackageManager.PERMISSION_GRANTED) {
            createCameraSource();
        } else {
            requestCameraPermission();
        }


        ////**********************************//////////
        ////**********************************//////////
        ////**********************************//////////
        //// VARIABLES FOR ACTIONABLE EMOTION DETECTION/
        ////**********************************//////////
        ////**********************************//////////
        sax_vector=new Vector<Integer>();
        sax_vector_times=new Vector<String>();
        physical_activity_vector=new Vector<Float>();
        physical_activity_vector_times=new Vector<String>();
        microphone_vector=new Vector<Float>();
        microphone_vector_times=new Vector<String>();
        subjects_vector=new Vector<Integer>();
        subjects_vector_times=new Vector<String>();
        microphone_tmp_sum=0.0f;
        microphone_tmp_sum_count=0;
        is_conversation=false;
        is_noise=false;
        current_number_of_subject=0;
        count_service=0;
        was_stressed_by_service=false;

        lock_physical_activity=false;
        lock_noise=false;
        lock_conversation=false;
        lock_emotional_trigger=false;

        EDA_vector_emotional_trigger=new Vector<Float>();
        eda_count_emotional_trigger=1;
        TextView_emotional_trigger=(TextView) findViewById(R.id.TextView_emotional_trigger);



        float d=1;
        float k=6;  //tamaño de todo el vector
        float k_1=3; //tamaño de la subsecuencia a
        float k_2=3; //tamaño de la subsecuencia b
        float tmp1=1/k_1;
        float tmp2=1/k_2;
        float a_adwin=1/(tmp1+tmp2);
        e_cut= (float) sqrt((1/(2*a_adwin))*(Math.log((k*4)/d)));


        is_connecting=false;
        count_seconds_microphone=0;



        ///****Start Empatica API****///
        initEmpaticaDeviceManager();
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, @NonNull String[] permissions, @NonNull int[] grantResults) {
        switch (requestCode) {
            case REQUEST_PERMISSION_ACCESS_COARSE_LOCATION:
                // If request is cancelled, the result arrays are empty.
                if (grantResults.length > 0 && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
                    // Permission was granted, yay!
                    initEmpaticaDeviceManager();
                } else {
                    // Permission denied, boo!
                    final boolean needRationale = ActivityCompat.shouldShowRequestPermissionRationale(this, Manifest.permission.ACCESS_COARSE_LOCATION);
                    new AlertDialog.Builder(this)
                            .setTitle("Permission required")
                            .setMessage("Without this permission bluetooth low energy devices cannot be found, allow it in order to connect to the device.")
                            .setPositiveButton("Retry", new DialogInterface.OnClickListener() {
                                public void onClick(DialogInterface dialog, int which) {
                                    // try again
                                    if (needRationale) {
                                        // the "never ask again" flash is not set, try again with permission request
                                        initEmpaticaDeviceManager();
                                    } else {
                                        // the "never ask again" flag is set so the permission requests is disabled, try open app settings to enable the permission
                                        Intent intent = new Intent(Settings.ACTION_APPLICATION_DETAILS_SETTINGS);
                                        Uri uri = Uri.fromParts("package", getPackageName(), null);
                                        intent.setData(uri);
                                        startActivity(intent);
                                    }
                                }
                            })
                            .setNegativeButton("Exit application", new DialogInterface.OnClickListener() {
                                public void onClick(DialogInterface dialog, int which) {
                                    // without permission exit is the only way
                                    finish();
                                }
                            })
                            .show();
                }
                break;
        }
    }

    private void initEmpaticaDeviceManager() {
        // Android 6 (API level 23) now require ACCESS_COARSE_LOCATION permission to use BLE
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
            ActivityCompat.requestPermissions(this, new String[] { Manifest.permission.ACCESS_COARSE_LOCATION }, REQUEST_PERMISSION_ACCESS_COARSE_LOCATION);
        } else {
            // Create a new EmpaDeviceManager. MainActivity is both its data and status delegate.
            deviceManager = new EmpaDeviceManager(getApplicationContext(), this, this);

            if (TextUtils.isEmpty(EMPATICA_API_KEY)) {
                new AlertDialog.Builder(this)
                        .setTitle("Warning")
                        .setMessage("Please insert your API KEY")
                        .setNegativeButton("Close", new DialogInterface.OnClickListener() {
                            public void onClick(DialogInterface dialog, int which) {
                                // without permission exit is the only way
                                finish();
                            }
                        })
                        .show();
                return;
            }
            // Initialize the Device Manager using your API key. You need to have Internet access at this point.
            deviceManager.authenticateWithAPIKey(EMPATICA_API_KEY);
        }
    }

    @Override
    protected void onPause() {
        super.onPause();
        if (deviceManager != null) {
            deviceManager.stopScanning();
        }
        if(speaker !=null){
            speaker.stop();
            speaker.shutdown();
        }
        mPreview.stop();
    }
    @Override
    protected void onResume() {
        super.onResume();

        startCameraSource();
    }

    @Override
    protected void onDestroy() {
        super.onDestroy();
        if (deviceManager != null) {
            deviceManager.cleanUp();
        }
        if (mCameraSource != null) {
            mCameraSource.release();
        }

    }

    @Override
    public void didDiscoverDevice(BluetoothDevice bluetoothDevice, String deviceName, int rssi, boolean allowed) {
        // Check if the discovered device can be used with your API key. If allowed is always false,
        // the device is not linked with your API key. Please check your developer area at
        // https://www.empatica.com/connect/developer.php
        if (allowed) {
            // Stop scanning. The first allowed device will do.
            deviceManager.stopScanning();
            try {
                // Connect to the device
                deviceManager.connectDevice(bluetoothDevice);
                updateLabel(deviceNameLabel, "To: " + deviceName);


                //Franci:get the initial time
                Calendar c = Calendar.getInstance();
                initial_sec = c.get(Calendar.SECOND);
                initial_min = c.get(Calendar.MINUTE);
                initial_hou = c.get(Calendar.HOUR);

                last_minute=initial_min;
                last_second=initial_sec;
                eda_last_min=initial_min;
                last_second_microphone=initial_sec;
                last_minute_microphone=initial_min;
                is_connecting=true;


            } catch (ConnectionNotAllowedException e) {
                // This should happen only if you try to connect when allowed == false.
                Toast.makeText(MainActivity.this, "Sorry, you can't connect to this device", Toast.LENGTH_SHORT).show();
            }
        }
    }

    @Override
    public void didRequestEnableBluetooth() {
        // Request the user to enable Bluetooth
        Intent enableBtIntent = new Intent(BluetoothAdapter.ACTION_REQUEST_ENABLE);
        startActivityForResult(enableBtIntent, REQUEST_ENABLE_BT);
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        // The user chose not to enable Bluetooth
        if (requestCode == REQUEST_ENABLE_BT && resultCode == Activity.RESULT_CANCELED) {
            // You should deal with this
            return;
        }
        super.onActivityResult(requestCode, resultCode, data);
    }

    @Override
    public void didUpdateSensorStatus(EmpaSensorStatus status, EmpaSensorType type) {
        // No need to implement this right now
    }

    @Override
    public void didUpdateStatus(EmpaStatus status) {
        // Update the UI
        updateLabel(statusLabel, status.name());

        // The device manager is ready for use
        if (status == EmpaStatus.READY) {
            updateLabel(statusLabel, status.name() + " - Turn on your device");
            // Start scanning
            deviceManager.startScanning();
            // The device manager has established a connection
        } else if (status == EmpaStatus.CONNECTED) {
            // Stop streaming after STREAMING_TIME
            runOnUiThread(new Runnable() {
                @Override
                public void run() {
                    dataCnt.setVisibility(View.VISIBLE);
                    new Handler().postDelayed(new Runnable() {
                        @Override
                        public void run() {
                            // Disconnect device
                            deviceManager.disconnect();
                        }
                    }, STREAMING_TIME);
                }
            });
            // The device manager disconnected from a device
        } else if (status == EmpaStatus.DISCONNECTED) {
            updateLabel(deviceNameLabel, "");
        }
    }

    @Override
    public void didReceiveAcceleration(int x, int y, int z, double timestamp) {
        updateLabel(accel_xLabel, "" + x);
        updateLabel(accel_yLabel, "" + y);
        updateLabel(accel_zLabel, "" + z);

        //compute physical activity each 10 seconds
        c_ACC = Calendar.getInstance();
        seconds_ACC = c_ACC.get(Calendar.SECOND);
        minute_ACC = c_ACC.get(Calendar.MINUTE);
        hour_ACC = c_ACC.get(Calendar.HOUR);



        a_x_ACC=x/64;
        a_y_ACC=y/64;
        a_z_ACC=z/64;
        tmp_ACC=(float) Math.sqrt(a_x_ACC*a_x_ACC+a_y_ACC*a_y_ACC+a_z_ACC*a_z_ACC);
        magnitude_by_seconds.add(tmp_ACC);

        if(seconds_ACC!=last_second&&seconds_acc!=10)
        {
            seconds_acc++;
            last_second=seconds_ACC;
        }
        if(seconds_acc==10)
        {
            float sd=standard_d();
            general_magnitude.add(sd);
            magnitude_by_seconds.clear();
            seconds_acc=0;
            last_second=seconds_ACC;
            physical_activity_vector.add(sd);
            physical_activity_vector_times.add(String.valueOf(hour_ACC)+"-"+String.valueOf(minute_ACC)+"-"+String.valueOf(seconds_ACC));
            if(sd<0.21348) {
                updateLabel(TextView_physical_activity, "PHYSICAL ACTIVITY: Sitting-" + sd);
                physical_activity=0;
                //Log.i("PHYSICAL ACTIVITY: Sitting-" + sd,"");
            }
            else if(sd<1) {
                updateLabel(TextView_physical_activity, "PHYSICAL ACTIVITY: Walking-" + sd);
                physical_activity=1;
                //Log.i("PHYSICAL ACTIVITY: Walking-" + sd,"");
            }
            else {
                updateLabel(TextView_physical_activity, "PHYSICAL ACTIVITY: Running-" + sd);
                physical_activity=2;
                //Log.i("PHYSICAL ACTIVITY: Running-" + sd,"");
            }
        }
    }

    private float mean_acc()
    {
        float tmp=0;
        for(int i=0;i<magnitude_by_seconds.size(); i++)
        {
            tmp=tmp+magnitude_by_seconds.get(i);
        }
        return tmp/magnitude_by_seconds.size();
    }
    public float standard_d()
    {
        float c_mean=mean_acc();
        float tmp=0;
        float d;
        for(int i=0;i<magnitude_by_seconds.size(); i++)
        {
            d=magnitude_by_seconds.get(i)-c_mean;
            tmp=tmp+(d*d);
        }
        tmp=tmp/(magnitude_by_seconds.size()-1);
        return (float) Math.sqrt(tmp);
    }

    @Override
    public void didReceiveBVP(float bvp, double timestamp) {
        //updateLabel(bvpLabel, "" + bvp);
    }

    @Override
    public void didReceiveBatteryLevel(float battery, double timestamp) {
        updateLabel(batteryLabel, String.format("%.0f %%", battery * 100));
    }

    @Override
    public void didReceiveGSR(float gsr, double timestamp) {
        updateLabel(edaLabel, "" + gsr);

        /************************************************************************************/
        /////////**************Franci: Detecting stress changes*********************///////////
        /************************************************************************************/

        c_GSR = Calendar.getInstance();
        tmp_hour_GSR = c_GSR.get(Calendar.HOUR);
        tmp_min_GSR = c_GSR.get(Calendar.MINUTE);
        tmp_sec_GSR = c_GSR.get(Calendar.SECOND);


        ///******Computing Baseline*********///
        if(eda_is_baseline)//Making segments of 3 min for analysing stress
        {
            //Add EDA values to vectors
            eda_vector.add(gsr);
            eda_vector_window.add(gsr);
            /*Verify all variables of the sensors
            *ACC=(physical_activity) 0->Sitting
            *                        1->Walking
            *                        2->Running
            *MICROPHONE=Average each minute
            *                        is_conversation
            *                        is_noise
            *Number of Subjects
            *                       current_number_of_subject(0,1,2,3)
            *
            */

            if(is_noise&&!lock_noise&&!lock_emotional_trigger&&(experiment_count>4))
            {
                lock_noise=true;
                lock_emotional_trigger=true;
                type_of_emotional_trigger="Noise Audio Emotional Trigger";
                updateLabel(TextView_emotional_trigger,"EMOTIONAL TRIGGER: "+ "Noise Audio");
                Log.i("Emotional Trigger", "Noise Audio");
                tmp_sax_sensors=compute_current_sax();
            }
            if(current_number_of_subject>=2&&is_conversation&&!lock_conversation&&!lock_emotional_trigger&&(experiment_count>4))
            {
                lock_conversation=true;
                lock_emotional_trigger=true;
                type_of_emotional_trigger="Conversation Emotional Trigger";
                updateLabel(TextView_emotional_trigger,"EMOTIONAL TRIGGER: "+ "Conversation");
                Log.i("Emotional Trigger", "conversation");
                tmp_sax_sensors=compute_current_sax();
            }
            if((physical_activity==1||physical_activity==2)&&!lock_physical_activity&&!lock_emotional_trigger&&(experiment_count>4)&&(current_number_of_subject==0))
            {
                lock_physical_activity=true;
                lock_emotional_trigger=true;
                type_of_emotional_trigger="Physical Activity Emotional Trigger";
                updateLabel(TextView_emotional_trigger,"EMOTIONAL TRIGGER: "+ "Physical Activity");
                Log.i("Emotional Trigger", "physical activity");
                tmp_sax_sensors=compute_current_sax();
            }
            if(tmp_min_GSR!=eda_last_min) {
                if(lock_emotional_trigger)
                    eda_count_emotional_trigger++;
                eda_count++;
                experiment_count++;
                eda_last_min=tmp_min_GSR;
                Log.i("Franci says experiment count----->", String.valueOf(experiment_count));
                if(experiment_count==15||experiment_count==45||experiment_count==75)//Moments where is emited the service
                {
                    count_service++;
                    tmp_sax_sensors=compute_current_sax();
                    eda_count_emotional_trigger=1;
                    emit_service(count_service,was_stressed_by_service);
                    lock_emotional_trigger=true;
                    lock_physical_activity=true;
                    lock_conversation=true;
                    lock_noise=true;
                    EDA_vector_emotional_trigger.clear();
                    type_of_emotional_trigger="Software service Emotional Trigger";
                    updateLabel(TextView_emotional_trigger,"SOFTWARE SERVICE EMITED");
                }
                if(experiment_count==(experiment_time+5)) {//Save all data of experiment
                    writeToFile(subject_name);
                    Log.i("Franci Says---Write file--->","FILE WROTE");
                    updateLabel(TextView_stress,"FILE WROTE");
                }
            }
            if(lock_emotional_trigger){
                EDA_vector_emotional_trigger.add(gsr);
                if(eda_count_emotional_trigger==4)
                {
                    Log.i("Franci says experiment Emotional Trigger----->", "");
                    eda_count_emotional_trigger=1;
                    lock_emotional_trigger=false;
                    lock_physical_activity=false;
                    lock_noise=false;
                    lock_conversation=false;
                    if(EDA_vector_emotional_trigger.size()>100){
                        int current_sax=sax(EDA_vector_emotional_trigger);////
                        EDA_vector_emotional_trigger.clear();
                        sax_vector.add(current_sax);
                        if((tmp_sax_sensors-current_sax)>e_cut) {
                            updateLabel(TextView_emotional_trigger, "EMOTIONAL TRIGGER: Stressed");
                            sax_vector_times.add(String.valueOf(tmp_hour_GSR)+"-"+String.valueOf(tmp_min_GSR)+"-"+String.valueOf(tmp_sec_GSR)+" EMOTIONAL TRIGGER: "+type_of_emotional_trigger+"/ Stressed");
                            was_stressed_by_service=true;
                        }
                        else {
                            updateLabel(TextView_emotional_trigger, "EMOTIONAL TRIGGER: Not-Stressed");
                            sax_vector_times.add(String.valueOf(tmp_hour_GSR)+"-"+String.valueOf(tmp_min_GSR)+"-"+String.valueOf(tmp_sec_GSR)+" EMOTIONAL TRIGGER: "+type_of_emotional_trigger+"/Not-Stressed");
                            was_stressed_by_service=false;
                        }
                    }
                }}

            /*if(eda_count==4)//3 Min
            {
                Log.i("Franci says experiment El de siempre----->", "");
                eda_count=1;
                int current_sax=sax(eda_vector_window);
                sax_vector.add(current_sax);
                sax_vector_times.add(String.valueOf(tmp_hour)+"-"+String.valueOf(tmp_min)+"-"+String.valueOf(tmp_sec));
                eda_vector_window.clear();
                ////****ADWIN************

                int sax_preview=sax_vector.get(sax_vector.size()-1);
                if((sax_preview-current_sax)>e_cut)
                    updateLabel(TextView_stress,"STRESS STATE: "+"Stressed");
                else
                    updateLabel(TextView_stress,"STRESS STATE: "+"Not-Stressed");

            }*/
        }
        else{//computing the EDA baseline
            eda_vector_baseline.add(gsr);
            if((tmp_min_GSR-initial_min)==eda_min_baseline)
            {
                float tmp=compute_baseline();
                eda_baseline=tmp;
                updateLabel(TextView_baseline, "EDA_BASELINE: " + tmp);
                eda_is_baseline=true;
            }}
    }
    private float compute_baseline()
    {
        float tm;
        float sum=0;
        //Log.i("Franci Says XXX Size---->",String.valueOf(eda_vector_baseline.size()));
        for(int i=0;i<eda_vector_baseline.size();i++)
        {
            //Log.i("Franci Says XXX---->",String.valueOf(eda_vector_baseline.get(i)));
            tm=0;
            if(i<50)
            {
                for(int j=0;j<50+i;j++)
                {
                    tm=tm+eda_vector_baseline.get(j);
                }
                tm=tm/(50+i);
            }
            if (i>=(eda_vector_baseline.size()-50))
            {
                int hh=0;
                for(int j=i-50;j<eda_vector_baseline.size();j++)
                {
                    tm=tm+eda_vector_baseline.get(j);
                    hh++;
                }
                tm=tm/hh;
            }
            if (i>=50&&i<(eda_vector_baseline.size()-50)){
                for(int j=0;j<100;j++)
                {
                    tm=tm+eda_vector_baseline.get(i-50+j);
                }
                tm=tm/100;
            }
            sum=sum+tm;
            eda_vector_baseline_filtered.add(tm);
        }
        sum=sum/eda_vector_baseline_filtered.size();

        float c_mean=sum;
        float tmp=0;
        float d;
        for(int i=0;i<eda_vector_baseline_filtered.size(); i++)
        {
            d=eda_vector_baseline_filtered.get(i)-c_mean;
            tmp=tmp+(d*d);
        }
        tmp=tmp/(eda_vector_baseline_filtered.size()-1);
        eda_baseline_sd=(float) Math.sqrt(tmp);
        return sum;
    }





    private int compute_current_sax(){//window n=100

        Log.i("Franci says compute_current_sax----->Initial_Vector ", String.valueOf(eda_vector.size()));//*******filtering********///
        Vector <Float> f=new Vector<Float>();
        float tm;
        for(int i=0;i<eda_vector.size();i++)
        {
            tm=0;
            if(i<50)
            {
                for(int j=0;j<50+i;j++)
                {
                    tm=tm+eda_vector.get(j);
                }
                tm=tm/(50+i);
            }
            if (i>=(eda_vector.size()-50))
            {
                int hh=0;
                for(int j=i-50;j<eda_vector.size();j++)
                {
                    tm=tm+eda_vector.get(j);
                    hh++;
                }
                tm=tm/hh;
            }
            if (i>=50&&i<(eda_vector.size()-50)){
                for(int j=0;j<100;j++)
                {
                    tm=tm+eda_vector.get(i-50+j);
                }
                tm=tm/100;
            }

            f.add(tm);
        }
        Log.i("Franci says----->Filtered vector ", String.valueOf(f.size()));
        //******Aggregating ******
        Vector<Float> a=new Vector<Float>();
        float max;
        //Aggregated by
        int win=eda_number_log;//240
        for(int i=0;i<(f.size()/win);i++) {
            max = 0;
            for (int j = (win * i); j < win * i + win; j++) {
                if (max < f.get(j)) {
                    max = f.get(j);
                    //cout<<max<<endl;
                }
            }
            a.add(max);
        }
        Log.i("Franci says----->Vector_aggregated ", String.valueOf(a.size()));
        //*****Z-normalization/***********
        float mean=current_mean();
        float sd=current_sd(mean);
        float ro;
        Vector <Float> z=new Vector<Float>();
        for(int i=0;i<a.size();i++)
        {
            ro=(a.get(i)-mean)/sd;
            z.add(ro);
            Log.i("Franci says--Z-Norm----->", String.valueOf(ro));
        }

        /*******PAA*****////
        Vector<Float> c=new Vector<Float>();
        int n=z.size();
        int w=n/3;
        float c_i;
        int j_i;
        int j_f;
        for(int i=1;i<w+1;i++)
        {
            c_i=0;
            j_i=((n/w)*(i-1)+1);
            j_f=((n/w)*i);
            for(int j=j_i;j<=j_f;j++)
            {
                c_i=c_i+z.get(j-1);
            }
            c_i=(c_i*w)/n;
            c.add(c_i);
        }
        float current;
        current=c.get(c.size()-1);
        if(current<b_1)
            return 1;
        else if(current<b_2)
            return 2;
        else if(current<b_3)
            return 3;
        else if(current<b_4)
            return 4;
        else
            return 5;
    }


    private int sax(Vector<Float> eda_vector_window_tmp){//window n=100

        Log.i("Franci says sax----->Initial_Vector ", String.valueOf(eda_vector_window_tmp.size()));//*******filtering********///
        Vector <Float> f=new Vector<Float>();
        float tm;
        for(int i=0;i<eda_vector_window_tmp.size();i++)
        {
            tm=0;
            if(i<50)
            {
                for(int j=0;j<50+i;j++)
                {
                    tm=tm+eda_vector_window_tmp.get(j);
                }
                tm=tm/(50+i);
            }
            if (i>=(eda_vector_window_tmp.size()-50))
            {
                int hh=0;
                for(int j=i-50;j<eda_vector_window_tmp.size();j++)
                {
                    tm=tm+eda_vector_window_tmp.get(j);
                    hh++;
                }
                tm=tm/hh;
            }
            if (i>=50&&i<(eda_vector_window_tmp.size()-50)){
                for(int j=0;j<100;j++)
                {
                    tm=tm+eda_vector_window_tmp.get(i-50+j);
                }
                tm=tm/100;
            }

            f.add(tm);
        }
        Log.i("Franci says----->Filtered vector ", String.valueOf(f.size()));
        //******Aggregating ******
        Vector<Float> a=new Vector<Float>();
        float max;
        //Aggregated by
        int win=eda_number_log;//240
        for(int i=0;i<(f.size()/win);i++) {
            max = 0;
            for (int j = (win * i); j < win * i + win; j++) {
                if (max < f.get(j)) {
                    max = f.get(j);
                    //cout<<max<<endl;
                }
            }
            a.add(max);
        }
        Log.i("Franci says----->Vector_aggregated ", String.valueOf(a.size()));
        //*****Z-normalization/***********
        float mean=current_mean();
        float sd=current_sd(mean);
        float ro;
        Vector <Float> z=new Vector<Float>();
        for(int i=0;i<a.size();i++)
        {
            ro=(a.get(i)-mean)/sd;
            z.add(ro);
            Log.i("Franci says--Z-Norm----->", String.valueOf(ro));
        }

        /*******PAA*****////
        float paa=0;
        for(int i=0;i<z.size();i++)
        {
            paa=paa+z.get(i);
            Log.i("Franci says--Suma-PAA--Z[i]----->", String.valueOf(z.get(i)));
            Log.i("Franci says--Suma-PAA----->", String.valueOf(paa));
        }
        Log.i("Franci says--Suma----Final-PAA----->", String.valueOf(paa));
        paa=paa/eda_k;
        Log.i("Franci says--Final-PAA----->", String.valueOf(paa));
        //******Sax ****//

        if(paa<b_1)
            return 1;
        else if(paa<b_2)
            return 2;
        else if(paa<b_3)
            return 3;
        else if(paa<b_4)
            return 4;
        else
            return 5;

    }
    private float current_mean()
    {
        float mean=0;
        float tm;
        for(int i=0;i<eda_vector.size();i++)
        {
            tm=0;
            if(i<50)
            {
                for(int j=0;j<50+i;j++)
                {
                    tm=tm+eda_vector.get(j);
                }
                tm=tm/(50+i);
            }
            if (i>=(eda_vector.size()-50))
            {
                int hh=0;
                for(int j=i-50;j<eda_vector.size();j++)
                {
                    tm=tm+eda_vector.get(j);
                    hh++;
                }
                tm=tm/hh;
            }
            if (i>=50&&i<(eda_vector.size()-50)){
                for(int j=0;j<100;j++)
                {
                    tm=tm+eda_vector.get(i-50+j);
                }
                tm=tm/100;
            }
            mean=mean+tm;
        }

        for(int i=0;i<eda_vector_baseline_filtered.size();i++)
        {
            mean=mean+ eda_vector_baseline_filtered.get(i);
        }
        mean=mean/(eda_vector.size()+eda_vector_baseline_filtered.size());
        return mean;
    }
    private float current_sd(float mean)
    {
        float sd=0;
        float ro;
        for(int i=0;i<eda_vector_baseline_filtered.size();i++)
        {
            ro=(eda_vector_baseline_filtered.get(i)-mean);
            sd=sd+ ro*ro;
        }
        float tm;
        for(int i=0;i<eda_vector.size();i++)
        {
            tm=0;
            if(i<50)
            {
                for(int j=0;j<50+i;j++)
                {
                    tm=tm+eda_vector.get(j);
                }
                tm=tm/(50+i);
            }
            if (i>=(eda_vector.size()-50))
            {
                int hh=0;
                for(int j=i-50;j<eda_vector.size();j++)
                {
                    tm=tm+eda_vector.get(j);
                    hh++;
                }
                tm=tm/hh;
            }
            if (i>=50&&i<(eda_vector.size()-50)){
                for(int j=0;j<100;j++)
                {
                    tm=tm+eda_vector.get(i-50+j);
                }
                tm=tm/100;
            }
            ro=(tm-mean);
            sd=sd+ ro*ro;
        }
        sd=sd/(eda_vector.size()+eda_vector_baseline_filtered.size()-1);
        sd= (float) Math.sqrt(sd);
        return sd;
    }

    @Override
    public void didReceiveIBI(float ibi, double timestamp) {
        //updateLabel(ibiLabel, "" + ibi);
    }

    @Override
    public void didReceiveTemperature(float temp, double timestamp) {
        //updateLabel(temperatureLabel, "" + temp);
    }

    // Update a label with some text, making sure   this is run in the UI thread
    private void updateLabel(final TextView label, final String text) {
        runOnUiThread(new Runnable() {
            @Override
            public void run() {
                label.setText(text);
            }
        });
    }
    // Update a label with some text, making sure   this is run in the UI thread
    private void updateLabel_time(final TextView label, final String text) {
        Calendar c = Calendar.getInstance();
        final int seconds = c.get(Calendar.SECOND);
        final int minutes = c.get(Calendar.MINUTE);
        final int hours = c.get(Calendar.HOUR);
        runOnUiThread(new Runnable() {
            @Override
            public void run() {
                label.setText(text+"  time:  "+hours+":"+minutes+":"+seconds);
            }
        });
    }


//////////***************************************/////////////////////
//////////***************************************/////////////////////
        //Function to emit the message of health care reminder
//////////***************************************/////////////////////
//////////***************************************/////////////////////
private void emit_service(int type,boolean was_stressed) {
        //AudioManager am = (AudioManager)getSystemService(Context.AUDIO_SERVICE);
        if(type==1) {
            //am.setStreamVolume(am.STREAM_MUSIC, 15, 0);
            speaker.speak(message_5, TextToSpeech.QUEUE_FLUSH, null);
        }
        if(type==2)
        {
            if(was_stressed) {
                //am.setStreamVolume(am.STREAM_MUSIC, 10, 0);
                speaker.speak(message_2, TextToSpeech.QUEUE_FLUSH, null);
            }
            else{
                //am.setStreamVolume(am.STREAM_MUSIC, 10, 0);
                speaker.speak(message_3, TextToSpeech.QUEUE_FLUSH, null);
            }
        }
        if(type==3)
        {
            if(was_stressed) {
                //am.setStreamVolume(am.STREAM_MUSIC, 15, 0);
                speaker.speak(message_1, TextToSpeech.QUEUE_FLUSH, null);
            }
            else{
                //am.setStreamVolume(am.STREAM_MUSIC, 15  , 0);
                speaker.speak(message_1, TextToSpeech.QUEUE_FLUSH, null);
            }
        }

    }
//////////***************************************/////////////////////
//////////***************************************/////////////////////
    //Function to write all data of the experiment
//////////***************************************/////////////////////
//////////***************************************/////////////////////
public  void writeToFile(String fileName){
        FileOutputStream fos = null;
        try {
            final File dir = new File(Environment.getExternalStorageDirectory().getAbsolutePath() );
            if (!dir.exists())
            {
                if(!dir.mkdirs()){
                    Log.e("ALERT","could not create the directories");
                }
            }
            final File myFile = new File(dir, fileName + ".txt");
            if (!myFile.exists())
            {
                myFile.createNewFile();
            }
            fos = new FileOutputStream(myFile);
            String tmp="Actionable Emotion Detection in context-aware system";
            fos.write(tmp.getBytes());
            fos.write(System.getProperty("line.separator").getBytes());
            tmp="Subject: "+subject_name+" /Age: "+subject_age+" /Gender"+subject_gender+" /Occupation: "+subject_occupation;
            fos.write(tmp.getBytes());
            fos.write(System.getProperty("line.separator").getBytes());
            tmp="Initial time: "+String.valueOf(initial_hou)+":"+String.valueOf(initial_min)+":"+String.valueOf(initial_sec);
            fos.write(tmp.getBytes());
            fos.write(System.getProperty("line.separator").getBytes());
            tmp="Computed Sax vectors";
            fos.write(tmp.getBytes());
            fos.write(System.getProperty("line.separator").getBytes());
            for(int i=0;i<sax_vector.size();i++)
            {
                tmp=String.valueOf(sax_vector.get(i))+"--->"+String.valueOf(sax_vector_times.get(i));
                fos.write(tmp.getBytes());
                fos.write(System.getProperty("line.separator").getBytes());
            }
            tmp="Computed Physical Activity each 5 sec";
            fos.write(tmp.getBytes());
            fos.write(System.getProperty("line.separator").getBytes());
            for(int i=0;i<physical_activity_vector.size();i++)
            {
                tmp=String.valueOf(physical_activity_vector.get(i))+"--->"+String.valueOf(physical_activity_vector_times.get(i));
                fos.write(tmp.getBytes());
                fos.write(System.getProperty("line.separator").getBytes());
            }
            tmp="Computed dB by microphone";
            fos.write(tmp.getBytes());
            fos.write(System.getProperty("line.separator").getBytes());
            for(int i=0;i<microphone_vector.size();i++)
            {
                tmp=String.valueOf(microphone_vector.get(i))+"--->"+String.valueOf(microphone_vector_times.get(i));
                fos.write(tmp.getBytes());
                fos.write(System.getProperty("line.separator").getBytes());
            }
            tmp="Number of subjects recognized";
            fos.write(tmp.getBytes());
            fos.write(System.getProperty("line.separator").getBytes());
            for(int i=0;i<subjects_vector.size();i++)
            {
                tmp=String.valueOf(subjects_vector.get(i))+"--->"+String.valueOf(subjects_vector_times.get(i));
                fos.write(tmp.getBytes());
                fos.write(System.getProperty("line.separator").getBytes());
            }
            tmp="EDA baseline values";
            fos.write(tmp.getBytes());
            fos.write(System.getProperty("line.separator").getBytes());
            for(int i=0;i<eda_vector_baseline.size();i++)
            {
                tmp=String.valueOf(eda_vector_baseline.get(i));
                fos.write(tmp.getBytes());
                fos.write(System.getProperty("line.separator").getBytes());
            }
            tmp="EDA Values";
            fos.write(tmp.getBytes());
            fos.write(System.getProperty("line.separator").getBytes());
            for(int i=0;i<eda_vector.size();i++)
            {
                tmp=String.valueOf(eda_vector.get(i));
                fos.write(tmp.getBytes());
                fos.write(System.getProperty("line.separator").getBytes());
            }
            fos.close();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
//////////***************************************/////////////////////
//////////***************************************/////////////////////
    //Operations of the audio amplitude
//////////***************************************/////////////////////
//////////***************************************/////////////////////
private void precalculateWeightedA() {
    for (int i = 0; i < BLOCK_SIZE_FFT; i++) {
        double actualFreq = FREQRESOLUTION * i;
        double actualFreqSQ = actualFreq * actualFreq;
        double actualFreqFour = actualFreqSQ * actualFreqSQ;
        double actualFreqEight = actualFreqFour * actualFreqFour;

        double t1 = 20.598997 * 20.598997 + actualFreqSQ;
        t1 = t1 * t1;
        double t2 = 107.65265 * 107.65265 + actualFreqSQ;
        double t3 = 737.86223 * 737.86223 + actualFreqSQ;
        double t4 = 12194.217 * 12194.217 + actualFreqSQ;
        t4 = t4 * t4;

        double weightFormula = (3.5041384e16 * actualFreqEight)
                / (t1 * t2 * t3 * t4);

        weightedA[i] = weightFormula;
    }
}
private void startRecording(final float gain, final int finalCountTimeDisplay, final int finalCountTimeLog) {

        getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        recorder = new AudioRecord(MediaRecorder.AudioSource.VOICE_RECOGNITION,
                RECORDER_SAMPLERATE, RECORDER_CHANNELS,
                RECORDER_AUDIO_ENCODING, BLOCK_SIZE * BYTES_PER_ELEMENT);
        if (recorder.getState() == 1)
            Log.d("nostro log", "Il recorder è pronto");
        else
            Log.d("nostro log", "Il recorder non è pronto");

        recorder.startRecording();
        isRecording = true;
        // Creo una fft da BLOCK_SIZE_FFT punti --> BLOCK_SIZE_FFT / 2 bande utili,
        // ognuna da FREQRESOLUTION Hz
        fft = new DoubleFFT_1D(BLOCK_SIZE_FFT);

        recordingThread = new Thread(new Runnable() {
            public void run() {

                // Array di raw data (tot : BLOCK_SIZE_FFT * 2 bytes)
                short rawData[] = new short[BLOCK_SIZE_FFT];

                // Array di mag non pesati (BLOCK_SIZE_FFT / 2 perchè è il numero di
                // bande utili)
                final float dbFft[] = new float[BLOCK_SIZE_FFT / 2];

                // Array di mag pesati
                final float dbFftA[] = new float[BLOCK_SIZE_FFT / 2];

                float normalizedRawData;

                // La fft lavora con double e con numeri complessi (re + im in
                // sequenza)
                double[] audioDataForFFT = new double[BLOCK_SIZE_FFT * 2];

                // Soglia di udibilita (20*10^(-6))
                float amplitudeRef = 0.00002f;
                // terzi ottave
                final float[] dbBand = new float[THIRD_OCTAVE.length];

                final float[] linearBand = new float[THIRD_OCTAVE.length];
                final float[] linearBandCount = new float[THIRD_OCTAVE.length];
                int n = 3;

                // Variabili per calcolo medie Time Display
                int indexTimeDisplay = 1;
                double linearATimeDisplay = 0;


                // Variabili per calcolo medie Time Log
                int indexTimeLog = 0;
                double linearTimeLog = 0;
                double linearATimeLog = 0;
                final float[] linearBandTimeLog = new float[THIRD_OCTAVE.length];

                final float linearFftTimeDisplay[] = new float[BLOCK_SIZE_FFT / 2];
                final float linearFftATimeDisplay[] = new float[BLOCK_SIZE_FFT / 2];
                int initial_delay = 0;
                while (isRecording) {
                    // Leggo i dati
                    recorder.read(rawData, 0, BLOCK_SIZE_FFT);
                    // inserito un delay iniziale perché all'attivazione si avevano livelli molto alti di running leq (>100 dB) e minimi bassi (10 dB) dovuti forse all'attivazione inizale della periferica
                    initial_delay++;
                    if (initial_delay > 20) {
                        for (int i = 0, j = 0; i < BLOCK_SIZE_FFT; i++, j += 2) {
                            // Range [-1,1]
                            normalizedRawData = (float) rawData[i]
                                    / (float) Short.MAX_VALUE;
                            filter = normalizedRawData;
                            // Finestra di Hannings
                            double x = (2 * Math.PI * i) / (BLOCK_SIZE_FFT - 1);
                            double winValue = (1 - Math.cos(x)) * 0.5d;
                            // Parte reale
                            audioDataForFFT[j] = filter * winValue;
                            // Parte immaginaria
                            audioDataForFFT[j + 1] = 0.0;
                        }
                        // FFT
                        fft.complexForward(audioDataForFFT);
                        // Magsum non pesati
                        double linearFftGlobal = 0;
                        // Magsum pesati
                        double linearFftAGlobal = 0;
                        // indice per terzi ottava
                        int k = 0;
                        for (int ki = 0; ki < THIRD_OCTAVE.length; ki++) {
                            linearBandCount[ki] = 0;
                            linearBand[ki] = 0;
                            dbBand[ki] = 0;
                        }
                        // Leggo fino a BLOCK_SIZE_FFT/2 perchè in tot ho BLOCK_SIZE_FFT/2
                        // bande utili
                        for (int i = 0, j = 0; i < BLOCK_SIZE_FFT / 2; i++, j += 2) {
                            double re = audioDataForFFT[j];
                            double im = audioDataForFFT[j + 1];
                            // Magnitudo
                            double mag = Math.sqrt((re * re) + (im * im));
                            // Ponderata A
                            // da capire: per i = 0 viene un valore non valido (forse meno infinito), ma ha senso?
                            // questo si ritrova poi nel grafico:
                            // per i=0 la non pesata ha un valore, mentre la pesata non ce l'ha...
                            double weightFormula = weightedA[i];
                            dbFft[i] = (float) (10 * Math.log10(mag * mag
                                    / amplitudeRef))
                                    + (float) gain;
                            dbFftA[i] = (float) (10 * Math.log10(mag * mag
                                    * weightFormula
                                    / amplitudeRef))
                                    + (float) gain;
                            linearFftGlobal += Math.pow(10, (float) dbFft[i] / 10f);
                            linearFftAGlobal += Math.pow(10, (float) dbFftA[i] / 10f);
                            float linearFft = (float) Math.pow(10, (float) dbFft[i] / 10f);
                            if ((0 <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 17.8f)) {
                                linearBandCount[0] += 1;
                                linearBand[0] += linearFft;
                                dbBand[0] = (float) (10 * Math.log10(linearBand[0]));
                            }
                            if ((17.8f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 22.4f)) {
                                linearBandCount[1] += 1;
                                linearBand[1] += linearFft;
                                dbBand[1] = (float) (10 * Math.log10(linearBand[1]));
                            }
                            if ((22.4f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 28.2f)) {
                                linearBandCount[2] += 1;
                                linearBand[2] += linearFft;
                                dbBand[2] = (float) (10 * Math.log10(linearBand[2]));
                            }
                            if ((28.2f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 35.5f)) {
                                linearBandCount[3] += 1;
                                linearBand[3] += linearFft;
                                dbBand[3] = (float) (10 * Math.log10(linearBand[3]));
                            }
                            if ((35.5f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 44.7f)) {
                                linearBandCount[4] += 1;
                                linearBand[4] += linearFft;
                                dbBand[4] = (float) (10 * Math.log10(linearBand[4]));
                            }
                            if ((44.7f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 56.2f)) {
                                linearBandCount[5] += 1;
                                linearBand[5] += linearFft;
                                dbBand[5] = (float) (10 * Math.log10(linearBand[5]));
                            }
                            if ((56.2f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 70.8f)) {
                                linearBandCount[6] += 1;
                                linearBand[6] += linearFft;
                                dbBand[6] = (float) (10 * Math.log10(linearBand[6]));
                            }
                            if ((70.8f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 89.1f)) {
                                linearBandCount[7] += 1;
                                linearBand[7] += linearFft;
                                dbBand[7] = (float) (10 * Math.log10(linearBand[7]));
                            }
                            if ((89.1f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 112f)) {
                                linearBandCount[8] += 1;
                                linearBand[8] += linearFft;
                                dbBand[8] = (float) (10 * Math.log10(linearBand[8]));
                            }
                            if ((112f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 141f)) {
                                linearBandCount[9] += 1;
                                linearBand[9] += linearFft;
                                dbBand[9] = (float) (10 * Math.log10(linearBand[9]));
                            }
                            if ((141f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 178f)) {
                                linearBandCount[10] += 1;
                                linearBand[10] += linearFft;
                                dbBand[10] = (float) (10 * Math.log10(linearBand[10]));
                            }
                            if ((178f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 224f)) {
                                linearBandCount[11] += 1;
                                linearBand[11] += linearFft;
                                dbBand[11] = (float) (10 * Math.log10(linearBand[11]));
                            }
                            if ((224f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 282f)) {
                                linearBandCount[12] += 1;
                                linearBand[12] += linearFft;
                                dbBand[12] = (float) (10 * Math.log10(linearBand[12]));
                            }
                            if ((282f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 355f)) {
                                linearBandCount[13] += 1;
                                linearBand[13] += linearFft;
                                dbBand[13] = (float) (10 * Math.log10(linearBand[13]));
                            }
                            if ((355f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 447f)) {
                                linearBandCount[14] += 1;
                                linearBand[14] += linearFft;
                                dbBand[14] = (float) (10 * Math.log10(linearBand[14]));
                            }
                            if ((447f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 562f)) {
                                linearBandCount[15] += 1;
                                linearBand[15] += linearFft;
                                dbBand[15] = (float) (10 * Math.log10(linearBand[15]));
                            }
                            if ((562f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 708f)) {
                                linearBandCount[16] += 1;
                                linearBand[16] += linearFft;
                                dbBand[16] = (float) (10 * Math.log10(linearBand[16]));
                            }
                            if ((708f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 891f)) {
                                linearBandCount[17] += 1;
                                linearBand[17] += linearFft;
                                dbBand[17] = (float) (10 * Math.log10(linearBand[17]));
                            }
                            if ((891f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 1122f)) {
                                linearBandCount[18] += 1;
                                linearBand[18] += linearFft;
                                dbBand[18] = (float) (10 * Math.log10(linearBand[18]));
                            }
                            if ((1122f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 1413f)) {
                                linearBandCount[19] += 1;
                                linearBand[19] += linearFft;
                                dbBand[19] = (float) (10 * Math.log10(linearBand[19]));
                            }
                            if ((1413f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 1778f)) {
                                linearBandCount[20] += 1;
                                linearBand[20] += linearFft;
                                dbBand[20] = (float) (10 * Math.log10(linearBand[20]));
                            }
                            if ((1778f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 2239f)) {
                                linearBandCount[21] += 1;
                                linearBand[21] += linearFft;
                                dbBand[21] = (float) (10 * Math.log10(linearBand[21]));
                            }
                            if ((2239f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 2818f)) {
                                linearBandCount[22] += 1;
                                linearBand[22] += linearFft;
                                dbBand[22] = (float) (10 * Math.log10(linearBand[22]));
                            }
                            if ((2818f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 3548f)) {
                                linearBandCount[23] += 1;
                                linearBand[23] += linearFft;
                                dbBand[23] = (float) (10 * Math.log10(linearBand[23]));
                            }
                            if ((3548f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 4467f)) {
                                linearBandCount[24] += 1;
                                linearBand[24] += linearFft;
                                dbBand[24] = (float) (10 * Math.log10(linearBand[24]));
                            }
                            if ((4467f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 5623f)) {
                                linearBandCount[25] += 1;
                                linearBand[25] += linearFft;
                                dbBand[25] = (float) (10 * Math.log10(linearBand[25]));
                            }
                            if ((5623f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 7079f)) {
                                linearBandCount[26] += 1;
                                linearBand[26] += linearFft;
                                dbBand[26] = (float) (10 * Math.log10(linearBand[26]));
                            }
                            if ((7079f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 8913f)) {
                                linearBandCount[27] += 1;
                                linearBand[27] += linearFft;
                                dbBand[27] = (float) (10 * Math.log10(linearBand[27]));
                            }
                            if ((8913f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 11220f)) {
                                linearBandCount[28] += 1;
                                linearBand[28] += linearFft;
                                dbBand[28] = (float) (10 * Math.log10(linearBand[28]));
                            }
                            if ((11220f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 14130f)) {
                                linearBandCount[29] += 1;
                                linearBand[29] += linearFft;
                                dbBand[29] = (float) (10 * Math.log10(linearBand[29]));
                            }
                            if ((14130f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 17780f)) {
                                linearBandCount[30] += 1;
                                linearBand[30] += linearFft;
                                dbBand[30] = (float) (10 * Math.log10(linearBand[30]));
                            }
                            if ((17780f <= i * FREQRESOLUTION) && (i * FREQRESOLUTION < 22390f)) {
                                linearBandCount[31] += 1;
                                linearBand[31] += linearFft;
                                dbBand[31] = (float) (10 * Math.log10(linearBand[31]));
                            }
                        }
                        final double dbFftAGlobal = 10 * Math.log10(linearFftAGlobal);
                        fftCount++;
                        linearFftAGlobalRunning += linearFftAGlobal;
                        dbFftAGlobalRunning = 10 * Math.log10(linearFftAGlobalRunning / fftCount);

                        for (int ki = 0; ki < THIRD_OCTAVE.length; ki++) {
                            linearBandRunning[ki] += linearBand[ki];
                            dbBandRunning[ki] = 10 * (float) Math.log10(linearBandRunning[ki] / fftCount);
                        }
                        linearATimeDisplay += linearFftAGlobal;
                        for (int i = 0; i < THIRD_OCTAVE.length; i++) {
                            linearBandTimeDisplay[i] += linearBand[i];
                        }
                        for (int i = 0; i < dbFftTimeDisplay.length; i++) {
                            linearFftTimeDisplay[i] +=  Math.pow(10, (float) dbFft[i] / 10f);
                            linearFftATimeDisplay[i] +=  Math.pow(10, (float) dbFftA[i] / 10f);
                        }
                        if (indexTimeDisplay < finalCountTimeDisplay) {
                            indexTimeDisplay++;
                        } else {
                            // dati timeDisplay e icona notifiche
                            dbATimeDisplay = 10 * Math.log10(linearATimeDisplay / finalCountTimeDisplay);
                            indexTimeDisplay = 1;
                            linearATimeDisplay = 0;
                            runOnUiThread(new Runnable() {
                                @Override
                                public void run() {

                                    c_microphone = Calendar.getInstance();
                                    seconds_microphone = c_microphone.get(Calendar.SECOND);
                                    minute_microphone = c_microphone.get(Calendar.MINUTE);
                                    hour_microphone = c_microphone.get(Calendar.HOUR);
                                    microphone_vector.add((float) dbATimeDisplay);
                                    microphone_vector_times.add(String.valueOf(hour_microphone)+"-"+String.valueOf(minute_microphone)+"-"+String.valueOf(seconds_microphone));
                                    microphone_tmp_sum=microphone_tmp_sum+(float)dbATimeDisplay;
                                    microphone_tmp_sum_count++;

                                    if (is_connecting)
                                    {
                                        if(seconds_microphone!=last_second_microphone&&count_seconds_microphone!=15)
                                        {
                                            count_seconds_microphone++;
                                            last_second_microphone=seconds_microphone;
                                        }
                                        if(count_seconds_microphone==15)
                                        {
                                            count_seconds_microphone=0;
                                            microphone_tmp_sum=microphone_tmp_sum/microphone_tmp_sum_count;
                                            if (microphone_tmp_sum > 40&&microphone_tmp_sum<65){//Conversation
                                                is_conversation=true;
                                                updateLabel(TextView_audio,"MICROPHONE: conversation "+dBformat(dbATimeDisplay)+"dB");
                                                Log.i("MICROPHONE_conversation",String.valueOf(microphone_tmp_sum));
                                            }
                                            else if (microphone_tmp_sum > 70){//Noise
                                                is_noise=true;
                                                updateLabel(TextView_audio,"MICROPHONE: noise "+dBformat(dbATimeDisplay)+"dB");
                                                Log.i("MICROPHONE_noise",String.valueOf(microphone_tmp_sum));
                                            }
                                            else
                                            {
                                                is_conversation=false;
                                                is_noise=false;
                                                updateLabel(TextView_audio,"MICROPHONE: normal "+dBformat(dbATimeDisplay)+"dB");
                                                Log.i("MICROPHONE_normal",String.valueOf(microphone_tmp_sum));
                                            }
                                            microphone_tmp_sum_count=0;
                                            microphone_tmp_sum=0.0f;
                                        }
                                    }


                                }
                            });
                        }
                    }
                } // while
            }
        }, "AudioRecorder Thread");
        recordingThread.start();
    }
private String dBformat(double dB) {
        return String.format(Locale.ENGLISH, "%.1f", dB);
    }
//////////***************************************/////////////////////
//////////***************************************/////////////////////
    //Functions for the camera
//////////***************************************/////////////////////
//////////***************************************/////////////////////
private void requestCameraPermission() {
    Log.w(TAG, "Camera permission is not granted. Requesting permission");

    final String[] permissions = new String[]{Manifest.permission.CAMERA};

    if (!ActivityCompat.shouldShowRequestPermissionRationale(this,
            Manifest.permission.CAMERA)) {
        ActivityCompat.requestPermissions(this, permissions, RC_HANDLE_CAMERA_PERM);
        return;
    }

    final Activity thisActivity = this;

    View.OnClickListener listener = new View.OnClickListener() {
        @Override
        public void onClick(View view) {
            ActivityCompat.requestPermissions(thisActivity, permissions,
                    RC_HANDLE_CAMERA_PERM);
        }
    };

    Snackbar.make(mGraphicOverlay, R.string.permission_camera_rationale,
            Snackbar.LENGTH_INDEFINITE)
            .setAction(R.string.ok, listener)
            .show();
}
/**
     * Creates and starts the camera.  Note that this uses a higher resolution in comparison
     * to other detection examples to enable the barcode detector to detect small barcodes
     * at long distances.
     */
private void createCameraSource() {

        Context context = getApplicationContext();
        FaceDetector detector = new FaceDetector.Builder(context)
                .setClassificationType(FaceDetector.ALL_CLASSIFICATIONS)
                .build();

        detector.setProcessor(
                new MultiProcessor.Builder<>(new GraphicFaceTrackerFactory())
                        .build());

        if (!detector.isOperational()) {
            // Note: The first time that an app using face API is installed on a device, GMS will
            // download a native library to the device in order to do detection.  Usually this
            // completes before the app is run for the first time.  But if that download has not yet
            // completed, then the above call will not detect any faces.
            //
            // isOperational() can be used to check if the required native library is currently
            // available.  The detector will automatically become operational once the library
            // download completes on device.
            Log.w(TAG, "Face detector dependencies are not yet available.");
        }

        mCameraSource = new CameraSource.Builder(context, detector)
                .setRequestedPreviewSize(640, 480)
                .setFacing(CameraSource.CAMERA_FACING_FRONT)// .CAMERA_FACING_BACK)
                .setRequestedFps(30.0f)
                .build();
    }

    /*
     * Callback for the result from requesting permissions. This method
     * is invoked for every call on {@link #requestPermissions(String[], int)}.
     * <p>
     * <strong>Note:</strong> It is possible that the permissions request interaction
     * with the user is interrupted. In this case you will receive empty permissions
     * and results arrays which should be treated as a cancellation.
     * </p>
     *
     * @param requestCode  The request code passed in {@link #requestPermissions(String[], int)}.
     * @param permissions  The requested permissions. Never null.
     * @param grantResults The grant results for the corresponding permissions
     *                     which is either {@link PackageManager#PERMISSION_GRANTED}
     *                     or {@link PackageManager#PERMISSION_DENIED}. Never null.
     * @see #requestPermissions(String[], int)
     */
    /* @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        if (requestCode != RC_HANDLE_CAMERA_PERM) {
            Log.d(TAG, "Got unexpected permission result: " + requestCode);
            super.onRequestPermissionsResult(requestCode, permissions, grantResults);
            return;
        }

        if (grantResults.length != 0 && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
            Log.d(TAG, "Camera permission granted - initialize the camera source");
            // we have permission, so create the camerasource
            createCameraSource();
            return;
        }

        Log.e(TAG, "Permission not granted: results len = " + grantResults.length +
                " Result code = " + (grantResults.length > 0 ? grantResults[0] : "(empty)"));

        DialogInterface.OnClickListener listener = new DialogInterface.OnClickListener() {
            public void onClick(DialogInterface dialog, int id) {
                finish();
            }
        };

        android.app.AlertDialog.Builder builder = new android.app.AlertDialog.Builder(this);
        builder.setTitle("Face Tracker sample")
                .setMessage(R.string.no_camera_permission)
                .setPositiveButton(R.string.ok, listener)
                .show();
    }*/

    //==============================================================================================
    // Camera Source Preview
    //==============================================================================================

/**
     * Starts or restarts the camera source, if it exists.  If the camera source doesn't exist yet
     * (e.g., because onResume was called before the camera source was created), this will be called
     * again when the camera source is created.
     */
private void startCameraSource() {

        // check that the device has play services available.
        int code = GoogleApiAvailability.getInstance().isGooglePlayServicesAvailable(
                getApplicationContext());
        if (code != ConnectionResult.SUCCESS) {
            Dialog dlg =
                    GoogleApiAvailability.getInstance().getErrorDialog(this, code, RC_HANDLE_GMS);
            dlg.show();
        }

        if (mCameraSource != null) {
            try {
                mPreview.start(mCameraSource, mGraphicOverlay);
            } catch (IOException e) {
                Log.e(TAG, "Unable to start camera source.", e);
                mCameraSource.release();
                mCameraSource = null;
            }
        }
    }

    //==============================================================================================
    // Graphic Face Tracker
    //==============================================================================================

    /**
     * Factory for creating a face tracker to be associated with a new face.  The multiprocessor
     * uses this factory to create face trackers as needed -- one for each individual.
     */
    private class GraphicFaceTrackerFactory implements MultiProcessor.Factory<Face> {
        @Override
        public Tracker<Face> create(Face face) {
            return new GraphicFaceTracker(mGraphicOverlay);
        }
    }

    /**
     * Face tracker for each detected individual. This maintains a face graphic within the app's
     * associated face overlay.
     */
    private class GraphicFaceTracker extends Tracker<Face> {
        private GraphicOverlay mOverlay;
        private FaceGraphic mFaceGraphic;

        GraphicFaceTracker(GraphicOverlay overlay) {
            mOverlay = overlay;
            mFaceGraphic = new FaceGraphic(overlay);
        }

        /**
         * Start tracking the detected face instance within the face overlay.
         */
        @Override
        public void onNewItem(int faceId, Face item) {
            mFaceGraphic.setId(faceId);
            //Log.i("Franci Says ----->",String.valueOf(faceId));
        }

        /**
         * Update the position/characteristics of the face within the overlay.
         */
        @Override
        public void onUpdate(FaceDetector.Detections<Face> detectionResults, Face face) {
            mOverlay.add(mFaceGraphic);
            mFaceGraphic.updateFace(face);
            SparseArray<Face> count=detectionResults.getDetectedItems();
            //Log.i("Franci Says ----->Number of subjects",String.valueOf(count.size()));
            updateLabel(TextView_subjects,"NUMBER OF SUBJECTS: "+String.valueOf(count.size()));
            Calendar c = Calendar.getInstance();
            final int seconds = c.get(Calendar.SECOND);
            final int minute = c.get(Calendar.MINUTE);
            final int hour = c.get(Calendar.HOUR);
            subjects_vector.add(count.size());
            subjects_vector_times.add(String.valueOf(hour)+"-"+String.valueOf(minute)+"-"+String.valueOf(seconds));
            current_number_of_subject=count.size();
        }

        /**
         * Hide the graphic when the corresponding face was not detected.  This can happen for
         * intermediate frames temporarily (e.g., if the face was momentarily blocked from
         * view).
         */
        @Override
        public void onMissing(FaceDetector.Detections<Face> detectionResults) {
            mOverlay.remove(mFaceGraphic);
            //Log.i("Franci Says ----->Number of subjects","Nada");
            updateLabel(TextView_subjects,"NUMBER OF SUBJECTS: "+String.valueOf(0));
            current_number_of_subject=0;
            //Log.i("Franci Says ----->Number of subjects","0");
        }
        /**
         * Called when the face is assumed to be gone for good. Remove the graphic annotation from
         * the overlay.
         */
        @Override
        public void onDone() {
            mOverlay.remove(mFaceGraphic);
        }
    }



}
