# openvpn_status_connector_http
when installed as a systemd service, it connects to openvpn management console via telnet and reports to http://10.8.0.1 

gcc executable_name source_file_path.c
sudo ./executable_name

/etc/systemd/system/itl_vpn_monitor.service ::
Description=ITL Server Script
After=network.target

[Service]
ExecStart=/home/user/10.8.0.1/server
Restart=on-failure
User=root
WorkingDirectory=/home/user/10.8.0.1
StandardOutput=journal
StandardError=journal

[Install]
WantedBy=multi-user.target
